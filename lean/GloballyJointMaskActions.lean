import CodedMaskChains
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Rebuild the global action along a chain of whole-group coded stages.
    Every source set is contained in a jointly coded invariant domain. -/
theorem countable_bafa_coded_mask_extension (base : BaseCollection s) (hB : BAFACode s) {w : U}
    (A : CodedMaskAction base w) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : InternalMask s w → U → U,
      (∀ a, ElementaryMap s s (J a) ∧ (∀ y, ∃ x, J a x = y) ∧ LocallyInternalTransitiveMap s (J a)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ a b x, J (internalMaskMul base a b) x = J a (J b x)) ∧
      (∀ a x y, CodedRelation s (A.maps a) x y → J a x = y) ∧
      (∀ a x, internalCode base (J a x) = internalCode base x) ∧
      (∀ d, ∃ t, Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) := by
  obtain ⟨C, hC⟩ := enumerated_coded_mask_chain base hB A enum henum
  refine ⟨codedMaskChainMap base C, ?_, coded_mask_chain_identity base C,
    coded_mask_chain_multiplication base C, ?_, ?_, coded_mask_chain_joint_covers base C⟩
  · intro a
    exact ⟨bijective_membership_elementary _ (iso_chain_map_injective (C.isoChain base a))
      (iso_chain_map_surjective (C.isoChain base a)) (iso_chain_map_members (C.isoChain base a)),
      iso_chain_map_surjective (C.isoChain base a), iso_chain_map_local (C.isoChain base a)⟩
  · intro a x y hxy
    apply iso_chain_map_value (C.isoChain base a)
    refine ⟨0, ?_⟩
    change CodedRelation s ((C.stage 0).maps a) x y
    rw [hC]
    exact hxy
  · intro a x
    exact (internal_code_eq base _ x).mpr
      (locally_internal_map_behavior base _ (iso_chain_map_local (C.isoChain base a)) x)

theorem countable_bafa_globally_joint_mask_action (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ P : InternalQuinePairs s w, ∃ J : InternalMask s w → U → U,
      (∀ a, ElementaryMap s s (J a) ∧ (∀ y, ∃ x, J a x = y) ∧ LocallyInternalTransitiveMap s (J a)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ a b x, J (internalMaskMul base a b) x = J a (J b x)) ∧
      (∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x) ∧
      (∀ a b x, J a (J b x) = J b (J a x)) ∧ (∀ a x, J a (J a x) = x) ∧
      (∀ a x, internalCode base (J a x) = internalCode base x) ∧
      (∀ d, ∃ t, Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) := by
  obtain ⟨z, w, hw, P, A, hAd, hAr, _⟩ := countable_bafa_joint_mask_extensions base hB enum henum
  obtain ⟨J, hJ, hOne, hMul, hExt, hQ, hCover⟩ := countable_bafa_coded_mask_extension base hB A enum henum
  refine ⟨z, w, hw, P, J, hJ, hOne, hMul, ?_, ?_, ?_, hQ, hCover⟩
  · intro a x hx
    exact hExt a x _ ((hAr a x _).mpr ⟨(hAd x).mpr hx, rfl⟩)
  · intro a b x
    exact group_action_preserves_commutation (internalMaskGroup base w) J hMul
      (internal_mask_mul_comm base a b) x
  · intro a x
    have h := hMul a a x
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (hOne x)

/-- Full PowerSet now holds for the actual rebuilt hereditary carrier.
    Full Separation, Collection and BAFA are not included. -/
theorem countable_bafa_mask_powerset_candidate (base : BaseCollection s) (hB : BAFACode s)
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
      ¬ ChoiceCode (maskSupportedMember J) := by
  obtain ⟨z, w, hw, P, J, hJ, _, _, hcore, hc, hs, _, hCover⟩ :=
    countable_bafa_globally_joint_mask_action base hB enum henum
  have hj : ∀ a, ElementaryMap s s (J a) := fun a => (hJ a).1
  have ho := fun a => (hJ a).2.1
  have hl := fun a => (hJ a).2.2
  exact ⟨z, w, hw, P, J, hJ, hc, hs, hcore, hCover,
    hereditary_mask_family base hw P J hj ho hcore,
    mask_carrier_extensional base.extensional J, mask_carrier_empty base hw J hj ho,
    mask_carrier_pairing base hw J hj, mask_carrier_union base J hj ho,
    mask_carrier_power_of_joint_covers base hj hc hs (fun d => hCover d.val),
    mask_carrier_infinity base hw J hl, mask_carrier_bounded_separation base hw J hj ho,
    mask_carrier_not_choice base hw P hj ho hcore⟩

#print axioms countable_bafa_globally_joint_mask_action
#print axioms countable_bafa_mask_powerset_candidate
end FullBridge
