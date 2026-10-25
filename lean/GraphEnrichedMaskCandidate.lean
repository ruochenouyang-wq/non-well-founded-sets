import FixedGraphAttachments
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- For each prescribed extensional source graph, construct one enriched
    candidate with a pointwise fixed injective solution range. The candidate
    may depend on the graph; its solution function is not asserted to be in H.
    Therefore this theorem does not assert BAFA inside H. -/
theorem countable_bafa_graph_enriched_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x)
    {a r : U} (hG : GraphCode s a r) (hExt : GraphExtensionalCode s a r) :
    ∃ z w, OmegaCode s z w ∧ ∃ P : InternalQuinePairs s w,
      ∃ J : InternalMask s w → U → U, ∃ f,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ i j x, J i (J j x) = J j (J i x)) ∧ (∀ i x, J i (J i x) = x) ∧
      (∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) ∧
      (∀ d, ∃ t, Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) ∧
      HereditarilyMaskSupported s w J P.family ∧
      Extensional (maskSupportedMember J) ∧ Empty (maskSupportedMember J) ∧
      Pairing (maskSupportedMember J) ∧ Union (maskSupportedMember J) ∧ PowerSet (maskSupportedMember J) ∧
      Infinity (maskSupportedMember J) ∧ BoundedSeparation (maskSupportedMember J) ∧
      PowerBoundedSeparation (maskSupportedMember J) ∧ ¬ChoiceCode (maskSupportedMember J) ∧
      DecorationCode s a r f ∧ InjectiveCode s f ∧
      (∀ i x X, CodedRelation s f x X → J i X = X) ∧
      (∀ x X, CodedRelation s f x X → HereditarilyMaskSupported s w J X) := by
  obtain ⟨z, w, hw, P, A, hAd, hAr, _⟩ := countable_bafa_joint_mask_extensions base hB enum henum
  obtain ⟨J, f, hJ, hOne, hMul, hOld, hCover, hf, hfi, hFix, hHer⟩ :=
    countable_bafa_fixed_graph_action base hB hw A hG hExt enum henum
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
    exact hOld i x _ ((hAr i x _).mpr ⟨(hAd x).mpr hx, rfl⟩)
  have hp := mask_carrier_pairing base hw J hj
  have hu := mask_carrier_union base J hj ho
  have hpow := mask_carrier_power_of_joint_covers base hj hc hs (fun d => hCover d.val)
  have hsep := mask_carrier_bounded_separation base hw J hj ho
  exact ⟨z, w, hw, P, J, f, hJ, hc, hs, hcore, hCover,
    hereditary_mask_family base hw P J hj ho hcore,
    mask_carrier_extensional base.extensional J, mask_carrier_empty base hw J hj ho,
    hp, hu, hpow, mask_carrier_infinity base hw J hl, hsep,
    power_bounded_separation_of_bounded hp hu hpow hsep, mask_carrier_not_choice base hw P hj ho hcore,
    hf, hfi, hFix, hHer⟩

#print axioms countable_bafa_graph_enriched_candidate
end FullBridge
