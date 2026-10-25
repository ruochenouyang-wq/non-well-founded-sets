import JointInternalMaskCores
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem mask_base_all_internally_covered {w : U} {J : InternalMask s w → U → U}
    (B : BaseCollection (maskSupportedMember J)) (X : MaskSupportedCarrier s w J) :
    InternalMaskCovered s w J X.val := by
  obtain ⟨T, hT, hXT⟩ := transitive_sets_cover B X
  exact ⟨T.val, (mask_transitive_iff T).mp hT, hXT,
    fun y hy => hereditary_mask_root (hereditary_mask_member T.property hy)⟩

theorem mask_uncovered_obstructs_full_base {w x : U} {J : InternalMask s w → U → U}
    (hx : HereditarilyMaskSupported s w J x) (hno : ¬ InternalMaskCovered s w J x) :
    ¬ BaseCollection (maskSupportedMember J) :=
  fun B => hno (mask_base_all_internally_covered B ⟨x, hx⟩)

theorem mask_base_hereditary_trace_exists (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (B : BaseCollection (maskSupportedMember J)) (a : U) :
    ∃ b, ∀ x, s x b ↔ s x a ∧ HereditarilyMaskSupported s w J x := by
  obtain ⟨b, hb⟩ := internal_mask_covered_trace_exists base hw hj hc hs hCover a
  refine ⟨b, fun x => (hb x).trans (and_congr Iff.rfl ?_)⟩
  exact ⟨internal_mask_covered_hereditary, fun hx => mask_base_all_internally_covered B ⟨x, hx⟩⟩

/-- The ambient bound may contain arbitrary extra objects. Only the selected
    actual-H witnesses must have internally supported transitive covers. -/
def MaskCoveredWitnessBounds (s : U → U → Prop) (w : U)
    (J : InternalMask s w → U → U) : Prop :=
  ∀ n (p : Formula (n+2)) (v : Fin n → MaskSupportedCarrier s w J) (a : MaskSupportedCarrier s w J),
    (∀ x, maskSupportedMember J x a → ∃ y, Eval (maskSupportedMember J) p (cons y (cons x v))) →
    ∃ b, ∀ x, maskSupportedMember J x a → ∃ y : MaskSupportedCarrier s w J,
      s y.val b ∧ InternalMaskCovered s w J y.val ∧ Eval (maskSupportedMember J) p (cons y (cons x v))

theorem mask_covered_witness_bounds_to_hereditary (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (hbound : MaskCoveredWitnessBounds s w J) : MaskHereditaryWitnessBounds s w J := by
  intro n p v a ht
  obtain ⟨b, hb⟩ := hbound n p v a ht
  obtain ⟨c, hc⟩ := internal_mask_covered_trace_exists base hw hj hc hs hCover b
  refine ⟨c, fun y hy => internal_mask_covered_hereditary ((hc y).mp hy).2, fun x hx => ?_⟩
  obtain ⟨y, hyb, hyc, hy⟩ := hb x hx
  exact ⟨y, (hc y.val).mpr ⟨hyb, hyc⟩, hy⟩

theorem mask_full_base_covered_witness_bounds {w : U} {J : InternalMask s w → U → U}
    (B : BaseCollection (maskSupportedMember J)) : MaskCoveredWitnessBounds s w J := by
  intro n p v a ht
  obtain ⟨b, hb⟩ := B.collection n p v a ht
  refine ⟨b.val, fun x hx => ?_⟩
  obtain ⟨y, hyb, hy⟩ := hb x hx
  exact ⟨y, hyb, mask_base_all_internally_covered B y, hy⟩

theorem mask_base_iff_covered_witness_bounds (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (ho : ∀ i y, ∃ x, J i x = y)
    (hl : ∀ i, LocallyInternalTransitiveMap s (J i))
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T) :
    BaseCollection (maskSupportedMember J) ↔ MaskCoveredWitnessBounds s w J := by
  constructor
  · exact mask_full_base_covered_witness_bounds
  · intro hbound
    have hc : ∀ i j x, J i (J j x) = J j (J i x) := fun i j x =>
      group_action_preserves_commutation (internalMaskGroup base w) J hMul (internal_mask_mul_comm base i j) x
    have hs : ∀ i x, J i (J i x) = x := by
      intro i x
      have h := hMul i i x
      rw [internal_mask_mul_self] at h
      exact h.symm.trans (hOne x)
    apply mask_witness_bounds_full_base base hw hj ho hl hOne hMul
      (fun d => by
        obtain ⟨T, _, hJ, hdT⟩ := hCover d
        exact ⟨T, hJ, hdT⟩)
    exact mask_covered_witness_bounds_to_hereditary base hw hj hc hs hCover hbound

#print axioms mask_base_iff_covered_witness_bounds
end FullBridge
