import MaskCoveredWitnesses
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Actual internally recognizable transitive cores in the same scheduled H.
    H itself is not replaced by the covered subclass in this theorem. -/
theorem countable_bafa_scheduled_internal_cores (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ J : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ i j x, J (internalMaskMul base i j) x = J i (J j x)) ∧
      (∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T) ∧
      Extensional (maskSupportedMember J) ∧ Empty (maskSupportedMember J) ∧
      Pairing (maskSupportedMember J) ∧ Union (maskSupportedMember J) ∧ PowerSet (maskSupportedMember J) ∧
      Infinity (maskSupportedMember J) ∧ BoundedSeparation (maskSupportedMember J) ∧
      PowerBoundedSeparation (maskSupportedMember J) ∧ BAFACode (maskSupportedMember J) ∧
      ¬ ChoiceCode (maskSupportedMember J) ∧
      (BaseCollection (maskSupportedMember J) ↔ MaskCoveredWitnessBounds s w J) ∧
      (Collection (maskSupportedMember J) ↔ BaseCollection (maskSupportedMember J)) ∧
      (∀ X : MaskSupportedCarrier s w J, ¬ InternalMaskCovered s w J X.val → ¬ Collection (maskSupportedMember J)) ∧
      (∀ a, ∃ b, ∀ x, s x b ↔ s x a ∧ InternalMaskCovered s w J x) ∧
      (Collection (maskSupportedMember J) →
        ∀ a, ∃ b, ∀ x, s x b ↔ s x a ∧ HereditarilyMaskSupported s w J x) ∧
      (∀ d, ∃ T C, Subset s d T ∧ TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧
        (∀ x, s x C ↔ s x T ∧ InternalMaskCovered s w J x) ∧
        TransitiveCode s C ∧ HereditarilyMaskSupported s w J C ∧ InternalMaskCovered s w J C ∧
        (∀ i, J i C = C) ∧ Nonempty (JointMaskDomain s w J C)) := by
  obtain ⟨z, w, hw, J, hJ, hOne, hMul, hCover, he, hem, hp, hu, hpow, hi, hsep, hpsep,
    hbafa, hnc, _, hCol, _, _, _⟩ := countable_bafa_scheduled_collection_reduction base hB enum henum
  have hj : ∀ i, ElementaryMap s s (J i) := fun i => (hJ i).1
  have ho := fun i => (hJ i).2.1
  have hl := fun i => (hJ i).2.2
  have hc : ∀ i j x, J i (J j x) = J j (J i x) := fun i j x =>
    group_action_preserves_commutation (internalMaskGroup base w) J hMul (internal_mask_mul_comm base i j) x
  have hs : ∀ i x, J i (J i x) = x := by
    intro i x
    have h := hMul i i x
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (hOne x)
  refine ⟨z, w, hw, J, hJ, hOne, hMul, hCover, he, hem, hp, hu, hpow, hi, hsep, hpsep, hbafa, hnc,
    mask_base_iff_covered_witness_bounds base hw hj ho hl hOne hMul hCover, hCol,
    fun X hn hcol => mask_uncovered_obstructs_full_base X.property hn (hCol.mp hcol),
    internal_mask_covered_trace_exists base hw hj hc hs hCover,
    fun hcol => mask_base_hereditary_trace_exists base hw hj hc hs hCover (hCol.mp hcol), ?_⟩
  intro d
  obtain ⟨T, hT, ⟨A⟩, hdT⟩ := hCover d
  obtain ⟨C, hC⟩ := joint_internal_mask_core_exists base hw A hT hj hc hs
  exact ⟨T, C, hdT, hT, ⟨A⟩, hC⟩

#print axioms countable_bafa_scheduled_internal_cores
end FullBridge
