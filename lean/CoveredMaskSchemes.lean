import CoveredMaskGraphs
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem covered_mask_extensional (he : Extensional s) {w : U} (J : InternalMask s w → U → U) :
    Extensional (coveredMaskMember J) := by
  intro a b hab
  apply Subtype.ext
  apply he
  intro x
  exact ⟨fun hx => (hab ⟨x, internal_mask_covered_member a.property hx⟩).mp hx,
    fun hx => (hab ⟨x, internal_mask_covered_member b.property hx⟩).mpr hx⟩

theorem covered_mask_empty (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    (J : InternalMask s w → U → U) (hj : ∀ i, ElementaryMap s s (J i))
    (ho : ∀ i y, ∃ x, J i x = y) : Empty (coveredMaskMember J) := by
  obtain ⟨e, he⟩ := base.empty
  have hH := hereditary_mask_empty base hw J hj ho he
  have ht : TransitiveCode s e := fun x hx => False.elim (he x hx)
  exact ⟨⟨e, hereditary_transitive_internal_mask_covered base.pairing base.union ht hH⟩, fun x hx => he x.val hx⟩

theorem covered_mask_pairing (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    (J : InternalMask s w → U → U) (hj : ∀ i, ElementaryMap s s (J i)) : Pairing (coveredMaskMember J) := by
  intro x y
  obtain ⟨p, hp⟩ := base.pairing x.val y.val
  exact ⟨⟨p, mask_covered_pair base hw hj x.property y.property hp⟩,
    fun a => (hp a.val).trans (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)⟩

theorem covered_mask_union (base : BaseCollection s) {w : U}
    (J : InternalMask s w → U → U) (hj : ∀ i, ElementaryMap s s (J i))
    (ho : ∀ i y, ∃ x, J i x = y) : Union (coveredMaskMember J) := by
  intro a
  obtain ⟨d, hd⟩ := base.union a.val
  refine ⟨⟨d, mask_covered_union base hj ho a.property hd⟩, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨y, hya, hxy⟩ := (hd x.val).mp hx
    exact ⟨⟨y, internal_mask_covered_member a.property hya⟩, hya, hxy⟩
  · rintro ⟨y, hya, hxy⟩
    exact (hd x.val).mpr ⟨y.val, hya, hxy⟩

theorem mask_covered_H_subset (hp : Pairing s) (hu : Union s) {w a b : U}
    {J : InternalMask s w → U → U} (ha : InternalMaskCovered s w J a)
    (hb : HereditarilyMaskSupported s w J b) (hba : Subset s b a) : InternalMaskCovered s w J b := by
  obtain ⟨C, hCt, haC, hroot⟩ := ha
  exact mask_covered_of_supported_subset hp hu hCt hroot (hereditary_mask_root hb)
    (fun y hy => hCt a haC y (hba y hy))

theorem covered_mask_cons_values {w : U} {J : InternalMask s w → U → U} {n}
    (x : CoveredMaskCarrier s w J) (v : Fin n → CoveredMaskCarrier s w J) :
    (fun i => (cons x v i).val) = cons x.val (fun i => (v i).val) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem covered_mask_bounded_absoluteness {w : U} {J : InternalMask s w → U → U} {n} (p : BoundedFormula n)
    (v : Fin n → CoveredMaskCarrier s w J) :
    BoundedEval (coveredMaskMember J) p v ↔ BoundedEval s p (fun i => (v i).val) := by
  induction p with
  | equal i j => exact ⟨congrArg Subtype.val, Subtype.ext⟩
  | member => rfl
  | bottom => rfl
  | conj p q hp hq => exact and_congr (hp v) (hq v)
  | impl p q hp hq => exact imp_congr (hp v) (hq v)
  | exMem i p hp =>
    constructor
    · rintro ⟨x, hx, hpx⟩
      exact ⟨x.val, hx, by simpa only [covered_mask_cons_values] using (hp (cons x v)).mp hpx⟩
    · rintro ⟨x, hx, hpx⟩
      let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member (v i).property hx⟩
      exact ⟨X, hx, (hp (cons X v)).mpr (by simpa only [covered_mask_cons_values] using hpx)⟩
  | allMem i p hp =>
    constructor
    · intro h x hx
      let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member (v i).property hx⟩
      simpa only [covered_mask_cons_values] using (hp (cons X v)).mp (h X hx)
    · intro h x hx
      exact (hp (cons x v)).mpr (by simpa only [covered_mask_cons_values] using h x.val hx)


theorem covered_mask_bounded_separation (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    (J : InternalMask s w → U → U) (hj : ∀ i, ElementaryMap s s (J i))
    (ho : ∀ i y, ∃ x, J i x = y) : BoundedSeparation (coveredMaskMember J) := by
  intro n p v a
  obtain ⟨b, hb⟩ := base.separation n p.toFormula (fun i => (v i).val) a.val
  have hH := hereditary_mask_source_separation base hw hj ho p.toFormula (fun i => (v i).val)
    (internal_mask_covered_hereditary a.property) (fun i => internal_mask_covered_hereditary (v i).property) hb
  have hcovered := mask_covered_H_subset base.pairing base.union a.property hH (fun y hy => ((hb y).mp hy).1)
  refine ⟨⟨b, hcovered⟩, fun x => ?_⟩
  have hsem := (bounded_eval_toFormula (s := s) p (cons x.val (fun i => (v i).val))).trans
    (by simpa only [covered_mask_cons_values] using (covered_mask_bounded_absoluteness p (cons x v)).symm)
  exact (hb x.val).trans (and_congr Iff.rfl hsem)

theorem covered_mask_infinity (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    (J : InternalMask s w → U → U) (hl : ∀ a, LocallyInternalTransitiveMap s (J a)) :
    Infinity (coveredMaskMember J) := by
  have hW := hereditary_mask_internally_wellFounded base hw hl (internal_omega_transitive base hw)
    (internal_omega_wellFounded base hw)
  have hWc := hereditary_transitive_internal_mask_covered base.pairing base.union
    (internal_omega_transitive base hw) hW
  let W : CoveredMaskCarrier s w J := ⟨w, hWc⟩
  let Z : CoveredMaskCarrier s w J := ⟨z, internal_mask_covered_member hWc hw.2.1.1⟩
  refine ⟨W, ⟨Z, hw.2.1.1, fun x hx => hw.1 x.val hx⟩, ?_⟩
  intro x hx
  obtain ⟨y, hxy⟩ := successor_exists base x.val
  have hyw := hw.2.1.2 x.val hx y hxy
  let Y : CoveredMaskCarrier s w J := ⟨y, internal_mask_covered_member hWc hyw⟩
  refine ⟨Y, hyw, fun t => ?_⟩
  exact (hxy t.val).trans (or_congr Iff.rfl ⟨Subtype.ext, congrArg Subtype.val⟩)

#print axioms covered_mask_bounded_separation
end FullBridge
