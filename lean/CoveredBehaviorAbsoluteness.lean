import CompleteCoveredModel
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop} {w : U} {J : InternalMask s w → U → U}

/-- Covered relation codes have absolute augmented bisimulation semantics. -/
theorem covered_mask_augmented_bisimulation_iff (r : CoveredMaskCarrier s w J) :
    Bisimulation (coveredMaskMember J) (WithIdentity (CodedRelation (coveredMaskMember J) r)) ↔
      Bisimulation s (WithIdentity (CodedRelation s r.val)) := by
  constructor
  · intro h x y hxy
    rcases hxy with rfl | hxy
    · exact ⟨fun a ha => ⟨a, ha, Or.inl rfl⟩, fun a ha => ⟨a, ha, Or.inl rfl⟩⟩
    · obtain ⟨hx, hy⟩ := covered_mask_relation_components r.property hxy
      let X : CoveredMaskCarrier s w J := ⟨x, hx⟩
      let Y : CoveredMaskCarrier s w J := ⟨y, hy⟩
      have hm := h X Y (Or.inr ((covered_mask_coded_relation_iff r X Y).mpr hxy))
      constructor
      · intro a ha
        let A : CoveredMaskCarrier s w J := ⟨a, internal_mask_covered_member hx ha⟩
        obtain ⟨B, hB, hAB⟩ := hm.1 A ha
        exact ⟨B.val, hB, hAB.elim (fun e => Or.inl (congrArg Subtype.val e))
          (fun e => Or.inr ((covered_mask_coded_relation_iff r A B).mp e))⟩
      · intro b hb
        let B : CoveredMaskCarrier s w J := ⟨b, internal_mask_covered_member hy hb⟩
        obtain ⟨A, hA, hAB⟩ := hm.2 B hb
        exact ⟨A.val, hA, hAB.elim (fun e => Or.inl (congrArg Subtype.val e))
          (fun e => Or.inr ((covered_mask_coded_relation_iff r A B).mp e))⟩
  · intro h X Y hXY
    have hxy : WithIdentity (CodedRelation s r.val) X.val Y.val :=
      hXY.elim (fun e => Or.inl (congrArg Subtype.val e))
        (fun e => Or.inr ((covered_mask_coded_relation_iff r X Y).mp e))
    constructor
    · intro A hA
      obtain ⟨b, hb, hab⟩ := (h X.val Y.val hxy).1 A.val hA
      let B : CoveredMaskCarrier s w J := ⟨b, internal_mask_covered_member Y.property hb⟩
      exact ⟨B, hb, hab.elim (fun e => Or.inl (Subtype.ext e))
        (fun e => Or.inr ((covered_mask_coded_relation_iff r A B).mpr e))⟩
    · intro B hB
      obtain ⟨a, ha, hab⟩ := (h X.val Y.val hxy).2 B.val hB
      let A : CoveredMaskCarrier s w J := ⟨a, internal_mask_covered_member X.property ha⟩
      exact ⟨A, ha, hab.elim (fun e => Or.inl (Subtype.ext e))
        (fun e => Or.inr ((covered_mask_coded_relation_iff r A B).mpr e))⟩

theorem covered_mask_internal_behavior_forward (x y : CoveredMaskCarrier s w J)
    (h : InternalBehavior (coveredMaskMember J) x y) : InternalBehavior s x.val y.val := by
  obtain ⟨r, hr, hxy⟩ := h
  exact ⟨r.val, (covered_mask_augmented_bisimulation_iff r).mp hr,
    hxy.elim (fun e => Or.inl (congrArg Subtype.val e))
      (fun e => Or.inr ((covered_mask_coded_relation_iff r x y).mp e))⟩

/-- Restrict source behavior to an invariant transitive covered core to
    obtain an actual covered witness; no full Hc schemes are assumed. -/
theorem covered_mask_internal_behavior_iff (base : BaseCollection s) {z : U}
    (hw : OmegaCode s z w) (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (x y : CoveredMaskCarrier s w J) :
    InternalBehavior (coveredMaskMember J) x y ↔ InternalBehavior s x.val y.val := by
  refine ⟨covered_mask_internal_behavior_forward x y, ?_⟩
  intro hxy
  obtain ⟨d, hd⟩ := base.pairing x.val y.val
  obtain ⟨T, hT, ⟨A⟩, hdT⟩ := hCover d
  obtain ⟨C, hm, hCt, hCH, _, hfix, _⟩ := joint_internal_mask_core_exists base hw A hT hj hc hs
  have hxC : s x.val C := (hm _).mpr ⟨hdT _ ((hd _).mpr (Or.inl rfl)), x.property⟩
  have hyC : s y.val C := (hm _).mpr ⟨hdT _ ((hd _).mpr (Or.inr rfl)), y.property⟩
  obtain ⟨r, hrG, hr⟩ := normalized_relation_comprehension base
    (internalBehaviorFormula 1 0 : Formula 2) Fin.elim0 C
  have hrel : ∀ a b, CodedRelation s r a b ↔ s a C ∧ s b C ∧ InternalBehavior s a b := by
    intro a b
    exact (hr a b).trans (and_congr_right (fun _ => and_congr_right
      (fun _ => eval_internalBehaviorFormula s 1 0 (cons b (cons a Fin.elim0)))))
  have hrfix : ∀ i, J i r = r := by
    intro i
    apply equivariant_relation_fixed base (hj i) (hs i)
      (fun p hp => by obtain ⟨a, b, _, _, hab⟩ := hrG p hp; exact ⟨a, b, hab⟩)
    intro a b hab
    obtain ⟨ha, hb, hab⟩ := (hrel a b).mp hab
    have hmem : ∀ t, s t C → s (J i t) C := by
      intro t ht
      have ht' := (hj i (Formula.member (n := 2) 0 1) (pairEnv t C)).mp ht
      change s (J i t) (J i C) at ht'
      simpa only [hfix i] using ht'
    exact (hrel _ _).mpr ⟨hmem a ha, hmem b hb, (elementary_map_internal_behavior (hj i) a b).mp hab⟩
  have hrH : HereditarilyMaskSupported s w J r := by
    apply hereditary_mask_intro ⟨z, hw.2.1.1, fun i _ => hrfix i⟩
    intro p hp
    obtain ⟨a, b, ha, hb, hab⟩ := hrG p hp
    exact hereditary_mask_ordered_pair base hw hj (hereditary_mask_member hCH ha)
      (hereditary_mask_member hCH hb) hab
  have hrc : InternalMaskCovered s w J r := mask_covered_normalized_relation base.pairing base.union
    hCt (fun a ha => hereditary_mask_root (hereditary_mask_member hCH ha)) hrH hrG
  have hrB : Bisimulation s (WithIdentity (CodedRelation s r)) := by
    intro a b hab
    rcases hab with rfl | hab
    · exact ⟨fun t ht => ⟨t, ht, Or.inl rfl⟩, fun t ht => ⟨t, ht, Or.inl rfl⟩⟩
    · obtain ⟨ha, hb, hab⟩ := (hrel a b).mp hab
      constructor
      · intro a' ha'
        obtain ⟨b', hb', hab'⟩ := (internalBehavior_bisimulation s a b hab).1 a' ha'
        exact ⟨b', hb', Or.inr ((hrel a' b').mpr ⟨hCt a ha a' ha', hCt b hb b' hb', hab'⟩)⟩
      · intro b' hb'
        obtain ⟨a', ha', hab'⟩ := (internalBehavior_bisimulation s a b hab).2 b' hb'
        exact ⟨a', ha', Or.inr ((hrel a' b').mpr ⟨hCt a ha a' ha', hCt b hb b' hb', hab'⟩)⟩
  let R : CoveredMaskCarrier s w J := ⟨r, hrc⟩
  exact ⟨R, (covered_mask_augmented_bisimulation_iff R).mpr hrB,
    Or.inr ((covered_mask_coded_relation_iff R x y).mpr ((hrel x.val y.val).mpr ⟨hxC, hyC, hxy⟩))⟩

#print axioms covered_mask_internal_behavior_iff
end FullBridge
