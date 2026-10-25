import UniversalMaskRealizations
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A single candidate has all prior axioms and realizes every compatible
    local coded action. Full Collection is still only characterized. -/
theorem countable_bafa_universal_covered_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ P : InternalQuinePairs s w, ∃ J : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ i j x, J (internalMaskMul base i j) x = J i (J j x)) ∧
      (∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) ∧
      (∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T) ∧
      CoveredCandidateLaws J ∧ UniversalMaskRealizations base J ∧
      (BaseCollection (coveredMaskMember J) ↔ CoveredTailFixedSourceBounds s w J) := by
  obtain ⟨z, w, hw, P, A, hd, hAr, _⟩ := countable_bafa_joint_mask_extensions base hB enum henum
  obtain ⟨J, hJ, hOne, hMul, hAJ, hCover, hBAFA, hUniversal⟩ :=
    countable_bafa_universal_mask_action base hB hw A enum henum
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
  have hcore : ∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x := by
    intro i x hx
    exact hAJ i x _ ((hAr i x _).mpr ⟨(hd x).mpr hx, rfl⟩)
  have hCover' : ∀ d, ∃ T, Nonempty (JointMaskDomain s w J T) ∧ Subset s d T := by
    intro d
    obtain ⟨T, _, hT, hdT⟩ := hCover d
    exact ⟨T, hT, hdT⟩
  have hp := covered_mask_pairing base hw J hj
  have hu := covered_mask_union base J hj ho
  have hpow := covered_mask_power base hj hc hs hCover'
  have hsep := covered_mask_bounded_separation base hw J hj ho
  have hlaws : CoveredCandidateLaws J :=
    ⟨covered_mask_extensional base.extensional J, covered_mask_empty base hw J hj ho,
      hp, hu, hpow, covered_mask_infinity base hw J hl, hsep,
      power_bounded_separation_of_bounded hp hu hpow hsep, covered_mask_bafa base hj hs hBAFA,
      covered_mask_not_choice base hw P hj ho hcore,
      covered_mask_transitive_containment base hw hj hc hs hCover⟩
  exact ⟨z, w, hw, P, J, hJ, hOne, hMul, hcore, hCover, hlaws, hUniversal,
    covered_base_iff_tail_fixed_source_bounds base hw hj hl hc hs hOne hMul hCover⟩

#print axioms countable_bafa_universal_covered_candidate
end FullBridge
