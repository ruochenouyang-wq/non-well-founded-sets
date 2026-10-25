import ScheduledNoChoiceCandidate
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Free variables [output,seed set,mask domain,joint family]. -/
def maskOrbitHullFormula : Formula 4 :=
  .ex (.ex (.conj (.member 1 4) (.conj (.member 0 3) (jointMaskPointFormula 5 1 0 2))))

theorem eval_maskOrbitHullFormula (y b G K : U) :
    Eval s maskOrbitHullFormula (cons y (cons b (cons G (cons K Fin.elim0)))) ↔
      ∃ i x, s i G ∧ s x b ∧ ∃ f, CodedRelation s K i f ∧ CodedRelation s f x y := by
  simp only [maskOrbitHullFormula, Eval, eval_jointMaskPointFormula]
  rfl

theorem joint_mask_orbit_hull_exists (base : BaseCollection s) {w T b : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J T) (hbT : Subset s b T) :
    ∃ c, Subset s c T ∧ ∀ y, s y c ↔ ∃ i : InternalMask s w, ∃ x, s x b ∧ J i x = y := by
  obtain ⟨c, hc⟩ := base.separation 3 maskOrbitHullFormula
    (cons b (cons A.masks (cons A.family Fin.elim0))) T
  have he : ∀ y, Eval s maskOrbitHullFormula
      (cons y (cons b (cons A.masks (cons A.family Fin.elim0)))) ↔
      ∃ i : InternalMask s w, ∃ x, s x b ∧ J i x = y := by
    intro y
    rw [eval_maskOrbitHullFormula]
    constructor
    · rintro ⟨i, x, hi, hx, f, hif, hxy⟩
      let I : InternalMask s w := ⟨i, (A.maskMembers i).mp hi⟩
      exact ⟨I, x, hx, (joint_mask_point_value A I (hbT x hx) y).mp ⟨f, hif, hxy⟩⟩
    · rintro ⟨i, x, hx, hy⟩
      exact ⟨i.val, x, (A.maskMembers i.val).mpr i.property, hx,
        (joint_mask_point_value A i (hbT x hx) y).mpr hy⟩
  refine ⟨c, fun y hy => ((hc y).mp hy).1, fun y => ?_⟩
  rw [hc, he]
  exact ⟨fun h => h.2, fun ⟨i, x, hx, hy⟩ => ⟨hy ▸ A.stable i x (hbT x hx), i, x, hx, hy⟩⟩

theorem hereditary_mask_orbit_bound (base : BaseCollection s) {z w b : U} (hw : OmegaCode s z w)
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ T, Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (hb : ∀ x, s x b → HereditarilyMaskSupported s w J x) :
    ∃ c, Subset s b c ∧ HereditarilyMaskSupported s w J c ∧
      (∀ i, J i c = c) ∧ ∀ y, s y c ↔ ∃ i : InternalMask s w, ∃ x, s x b ∧ J i x = y := by
  obtain ⟨T, ⟨A⟩, hbT⟩ := hCover b
  obtain ⟨c, _, hc⟩ := joint_mask_orbit_hull_exists base A hbT
  have hs : ∀ i x, J i (J i x) = x := by
    intro i x
    have h := hMul i i x
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (hOne x)
  have hcomm : ∀ i j x, J i (J j x) = J j (J i x) := fun i j x =>
    group_action_preserves_commutation (internalMaskGroup base w) J hMul (internal_mask_mul_comm base i j) x
  have hfixed : ∀ i, J i c = c := by
    intro i
    apply elementary_involution_closed_set base (hj i) (hs i)
    intro y hy
    obtain ⟨j, x, hx, rfl⟩ := (hc y).mp hy
    exact (hc _).mpr ⟨internalMaskMul base i j, x, hx, hMul i j x⟩
  have hH : HereditarilyMaskSupported s w J c := by
    apply hereditary_mask_intro ⟨z, hw.2.1.1, fun i _ => hfixed i⟩
    intro y hy
    obtain ⟨i, x, hx, rfl⟩ := (hc y).mp hy
    exact (hereditary_mask_invariant hj hcomm hs i x).mpr (hb x hx)
  exact ⟨c, fun x hx => (hc x).mpr ⟨internalMaskOne base w, x, hx, hOne x⟩, hH, hfixed, hc⟩

/-- The source bound need not itself have support. Its members must be
    hereditary, and the witness relation is evaluated inside H. -/
def MaskHereditaryWitnessBounds (s : U → U → Prop) (w : U)
    (J : InternalMask s w → U → U) : Prop :=
  ∀ n (p : Formula (n+2)) (v : Fin n → MaskSupportedCarrier s w J) (a : MaskSupportedCarrier s w J),
    (∀ x, maskSupportedMember J x a → ∃ y, Eval (maskSupportedMember J) p (cons y (cons x v))) →
    ∃ b, (∀ y, s y b → HereditarilyMaskSupported s w J y) ∧
      ∀ x, maskSupportedMember J x a → ∃ y : MaskSupportedCarrier s w J,
        s y.val b ∧ Eval (maskSupportedMember J) p (cons y (cons x v))

theorem mask_collection_iff_hereditary_witness_bounds (base : BaseCollection s)
    {z w : U} (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ T, Nonempty (JointMaskDomain s w J T) ∧ Subset s d T) :
    Collection (maskSupportedMember J) ↔ MaskHereditaryWitnessBounds s w J := by
  constructor
  · intro h n p v a ht
    obtain ⟨b, hb⟩ := h n p v a ht
    exact ⟨b.val, fun y hy => hereditary_mask_member b.property hy, hb⟩
  · intro h n p v a ht
    obtain ⟨b, hbH, hb⟩ := h n p v a ht
    obtain ⟨c, hbc, hcH, _, _⟩ := hereditary_mask_orbit_bound base hw hj hOne hMul hCover hbH
    refine ⟨⟨c, hcH⟩, ?_⟩
    intro x hx
    obtain ⟨y, hy, hp⟩ := hb x hx
    exact ⟨y, hbc y.val hy, hp⟩

#print axioms hereditary_mask_orbit_bound
#print axioms mask_collection_iff_hereditary_witness_bounds
end FullBridge
