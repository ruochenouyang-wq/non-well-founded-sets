import CoveredFixedInputCollection
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The pair family is already pointwise fixed by every mask. Passing to
    orbit inputs therefore does not remove this entire family from the
    remaining collection obligation. This is not a failure of Collection. -/
theorem covered_quine_family_pointwise_fixed (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (ho : ∀ i y, ∃ x, J i x = y)
    (hcore : ∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) :
    ∃ F : CoveredMaskCarrier s w J, F.val = P.family ∧
      ∀ x, coveredMaskMember J x F → ∀ i, J i x.val = x.val := by
  let F : CoveredMaskCarrier s w J := ⟨P.family, quine_pair_family_internally_covered base P
    (hereditary_mask_family base hw P J hj ho hcore)⟩
  exact ⟨F, rfl, fun x hx i => (global_mask_action_fixes_family base P J hj ho hcore i).1 x.val hx⟩

theorem covered_base_iff_tail_fixed_source_bounds (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hl : ∀ i, LocallyInternalTransitiveMap s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T) :
    BaseCollection (coveredMaskMember J) ↔ CoveredTailFixedSourceBounds s w J := by
  have ho : ∀ i y, ∃ x, J i x = y := fun i y => ⟨J i y, hs i y⟩
  have hiff := covered_collection_iff_tail_fixed_source_bounds base hw hj hc hs hOne hMul hCover
  constructor
  · exact fun h => hiff.mp h.collection
  · intro h
    have hp := covered_mask_pairing base hw J hj
    have hu := covered_mask_union base J hj ho
    have hsep := covered_mask_bounded_separation base hw J hj ho
    have hcol := hiff.mpr h
    have hCover' : ∀ d, ∃ T, Nonempty (JointMaskDomain s w J T) ∧ Subset s d T := by
      intro d
      obtain ⟨T, _, hT, hd⟩ := hCover d
      exact ⟨T, hT, hd⟩
    exact ⟨covered_mask_extensional base.extensional J, covered_mask_empty base hw J hj ho,
      hp, hu, covered_mask_power base hj hc hs hCover', covered_mask_infinity base hw J hl,
      collection_bounded_separation_full_separation hcol hp hu hsep, hcol⟩

/-- Actual scheduled candidate with the reduced collection obligation. The
    fixed-input source-bound condition is characterized, not asserted. -/
theorem countable_bafa_covered_fixed_input_reduction (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ J : InternalMask s w → U → U,
      Extensional (coveredMaskMember J) ∧ Empty (coveredMaskMember J) ∧
      Pairing (coveredMaskMember J) ∧ Union (coveredMaskMember J) ∧ PowerSet (coveredMaskMember J) ∧
      Infinity (coveredMaskMember J) ∧ BoundedSeparation (coveredMaskMember J) ∧
      PowerBoundedSeparation (coveredMaskMember J) ∧ BAFACode (coveredMaskMember J) ∧
      ¬ ChoiceCode (coveredMaskMember J) ∧
      (∀ x : CoveredMaskCarrier s w J, ∃ T, TransitiveCode (coveredMaskMember J) T ∧ coveredMaskMember J x T) ∧
      (Collection (coveredMaskMember J) ↔ CoveredTailFixedSourceBounds s w J) ∧
      (BaseCollection (coveredMaskMember J) ↔ CoveredTailFixedSourceBounds s w J) := by
  obtain ⟨z, w, hw, P, J, hJ, hOne, hMul, hc, hs, hcore, hCover, _, _, _, _, _, _, _, _, _, hBAFA, _⟩ :=
    countable_bafa_scheduled_scheme_criteria base hB enum henum
  have hj : ∀ i, ElementaryMap s s (J i) := fun i => (hJ i).1
  have ho := fun i => (hJ i).2.1
  have hl := fun i => (hJ i).2.2
  have hCover' : ∀ d, ∃ T, Nonempty (JointMaskDomain s w J T) ∧ Subset s d T := by
    intro d
    obtain ⟨T, _, hT, hd⟩ := hCover d
    exact ⟨T, hT, hd⟩
  have hp := covered_mask_pairing base hw J hj
  have hu := covered_mask_union base J hj ho
  have hpow := covered_mask_power base hj hc hs hCover'
  have hsep := covered_mask_bounded_separation base hw J hj ho
  exact ⟨z, w, hw, J, covered_mask_extensional base.extensional J,
    covered_mask_empty base hw J hj ho, hp, hu, hpow, covered_mask_infinity base hw J hl, hsep,
    power_bounded_separation_of_bounded hp hu hpow hsep,
    covered_mask_bafa base hj hs hBAFA, covered_mask_not_choice base hw P hj ho hcore,
    covered_mask_transitive_containment base hw hj hc hs hCover,
    covered_collection_iff_tail_fixed_source_bounds base hw hj hc hs hOne hMul hCover,
    covered_base_iff_tail_fixed_source_bounds base hw hj hl hc hs hOne hMul hCover⟩

#print axioms countable_bafa_covered_fixed_input_reduction
end FullBridge
