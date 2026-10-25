import PowerBoundedSeparation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem mask_carrier_power_bounded_separation (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ a, ElementaryMap s s (J a)) (ho : ∀ a y, ∃ x, J a x = y)
    (hc : ∀ a b x, J a (J b x) = J b (J a x)) (hs : ∀ a x, J a (J a x) = x)
    (hCover : ∀ d, ∃ t, Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) :
    PowerBoundedSeparation (maskSupportedMember J) := by
  exact power_bounded_separation_of_bounded
    (mask_carrier_pairing base hw J hj) (mask_carrier_union base J hj ho)
    (mask_carrier_power_of_joint_covers base hj hc hs (fun d => hCover d.val))
    (mask_carrier_bounded_separation base hw J hj ho)

/-- The new scheme holds in the same constructed carrier as PowerSet and
    failure of ChoiceCode. Full Separation, Collection and BAFA remain open. -/
theorem countable_bafa_mask_power_bounded_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ P : InternalQuinePairs s w, ∃ J : InternalMask s w → U → U,
      (∀ a, ElementaryMap s s (J a) ∧ (∀ y, ∃ x, J a x = y) ∧ LocallyInternalTransitiveMap s (J a)) ∧
      (∀ a b x, J a (J b x) = J b (J a x)) ∧ (∀ a x, J a (J a x) = x) ∧
      (∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x) ∧
      (∀ d, ∃ t, Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) ∧
      HereditarilyMaskSupported s w J P.family ∧
      Extensional (maskSupportedMember J) ∧ Empty (maskSupportedMember J) ∧
      Pairing (maskSupportedMember J) ∧ Union (maskSupportedMember J) ∧ PowerSet (maskSupportedMember J) ∧
      Infinity (maskSupportedMember J) ∧ BoundedSeparation (maskSupportedMember J) ∧
      PowerBoundedSeparation (maskSupportedMember J) ∧ ¬ ChoiceCode (maskSupportedMember J) := by
  obtain ⟨z, w, hw, P, J, hJ, hc, hs, hcore, hCover, hF, he, hem, hp, hu, hpow, hi, hsep, hnAC⟩ :=
    countable_bafa_mask_powerset_candidate base hB enum henum
  exact ⟨z, w, hw, P, J, hJ, hc, hs, hcore, hCover, hF, he, hem, hp, hu, hpow, hi, hsep,
    power_bounded_separation_of_bounded hp hu hpow hsep, hnAC⟩

#print axioms mask_carrier_power_bounded_separation
#print axioms countable_bafa_mask_power_bounded_candidate
end FullBridge
