import ScheduledMaskBAFA
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- One actual hereditary carrier satisfies full fixed-parameter BAFA,
    full PowerSet, bounded and power-bounded Separation, and failed Choice.
    Full Separation and Collection are still not included. -/
theorem countable_bafa_scheduled_no_choice_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ P : InternalQuinePairs s w, ∃ J : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ i j x, J i (J j x) = J j (J i x)) ∧ (∀ i x, J i (J i x) = x) ∧
      (∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) ∧
      (∀ d, ∃ t, TransitiveCode s t ∧ Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) ∧
      HereditarilyMaskSupported s w J P.family ∧
      Extensional (maskSupportedMember J) ∧ Empty (maskSupportedMember J) ∧
      Pairing (maskSupportedMember J) ∧ Union (maskSupportedMember J) ∧ PowerSet (maskSupportedMember J) ∧
      Infinity (maskSupportedMember J) ∧ BoundedSeparation (maskSupportedMember J) ∧
      PowerBoundedSeparation (maskSupportedMember J) ∧ BAFACode (maskSupportedMember J) ∧
      ¬ ChoiceCode (maskSupportedMember J) := by
  obtain ⟨z, w, hw, P, A, hd, hAr, _⟩ := countable_bafa_joint_mask_extensions base hB enum henum
  obtain ⟨J, hJ, hOne, hMul, hAJ, hCover, hBAFA⟩ := countable_bafa_scheduled_mask_action base hB hw A enum henum
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
  have hCover' : ∀ d, ∃ t, Nonempty (JointMaskDomain s w J t) ∧ Subset s d t := by
    intro d
    obtain ⟨t, _, hT, hdt⟩ := hCover d
    exact ⟨t, hT, hdt⟩
  have hp := mask_carrier_pairing base hw J hj
  have hu := mask_carrier_union base J hj ho
  have hpow := mask_carrier_power_of_joint_covers base hj hc hs (fun d => hCover' d.val)
  have hsep := mask_carrier_bounded_separation base hw J hj ho
  exact ⟨z, w, hw, P, J, hJ, hc, hs, hcore, hCover,
    hereditary_mask_family base hw P J hj ho hcore,
    mask_carrier_extensional base.extensional J, mask_carrier_empty base hw J hj ho,
    hp, hu, hpow, mask_carrier_infinity base hw J hl, hsep,
    power_bounded_separation_of_bounded hp hu hpow hsep, hBAFA,
    mask_carrier_not_choice base hw P hj ho hcore⟩

#print axioms countable_bafa_scheduled_no_choice_candidate
end FullBridge
