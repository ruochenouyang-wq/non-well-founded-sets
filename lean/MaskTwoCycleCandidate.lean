import MaskPartnerGraphs
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def TwoCycleCode (s : U → U → Prop) (x y : U) : Prop :=
  x ≠ y ∧ (∀ z, s z x ↔ z = y) ∧ (∀ z, s z y ↔ z = x)

theorem mask_two_cycle_iff {w : U} {J : InternalMask s w → U → U}
    (x y : MaskSupportedCarrier s w J) :
    TwoCycleCode (maskSupportedMember J) x y ↔ TwoCycleCode s x.val y.val := by
  constructor
  · rintro ⟨hne, hx, hy⟩
    refine ⟨fun h => hne (Subtype.ext h), ?_, ?_⟩
    · intro z
      constructor
      · intro hz
        exact congrArg Subtype.val ((hx ⟨z, hereditary_mask_member x.property hz⟩).mp hz)
      · intro hz
        exact hz.symm ▸ (hx y).mpr rfl
    · intro z
      constructor
      · intro hz
        exact congrArg Subtype.val ((hy ⟨z, hereditary_mask_member y.property hz⟩).mp hz)
      · intro hz
        exact hz.symm ▸ (hy x).mpr rfl
  · rintro ⟨hne, hx, hy⟩
    exact ⟨fun h => hne (congrArg Subtype.val h),
      fun z => (hx z.val).trans ⟨Subtype.ext, congrArg Subtype.val⟩,
      fun z => (hy z.val).trans ⟨Subtype.ext, congrArg Subtype.val⟩⟩

/-- The entire partner graph, its injective solution FUNCTION, and the
    transitive solution range are objects of one actual hereditary carrier.
    This is one full internal graph realization, not universal BAFA. -/
theorem countable_bafa_internal_two_cycle_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ P : InternalQuinePairs s w, ∃ J : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ i j x, J i (J j x) = J j (J i x)) ∧ (∀ i x, J i (J i x) = x) ∧
      (∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) ∧
      (∀ d, ∃ t, Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) ∧
      HereditarilyMaskSupported s w J P.family ∧
      Extensional (maskSupportedMember J) ∧ Empty (maskSupportedMember J) ∧
      Pairing (maskSupportedMember J) ∧ Union (maskSupportedMember J) ∧ PowerSet (maskSupportedMember J) ∧
      Infinity (maskSupportedMember J) ∧ BoundedSeparation (maskSupportedMember J) ∧
      PowerBoundedSeparation (maskSupportedMember J) ∧ ¬ChoiceCode (maskSupportedMember J) ∧
      ∃ d r f t : MaskSupportedCarrier s w J,
        (∀ x, s x d.val ↔ ∃ c, s c P.family ∧ s x c) ∧
        (∀ x y, CodedRelation s r.val x y ↔ s x d.val ∧ y = maskedLabelAction P w x) ∧
        GraphCode (maskSupportedMember J) d r ∧ GraphExtensionalCode (maskSupportedMember J) d r ∧
        DecorationCode (maskSupportedMember J) d r f ∧ InjectiveCode (maskSupportedMember J) f ∧
        RangeCode (maskSupportedMember J) d f t ∧ TransitiveCode (maskSupportedMember J) t ∧
        ∀ i l k, CodedRelation s P.leftCode i l → CodedRelation s P.rightCode i k →
          ∃ L K : MaskSupportedCarrier s w J,
            CodedRelation s f.val l L.val ∧ CodedRelation s f.val k K.val ∧
            TwoCycleCode (maskSupportedMember J) L K := by
  obtain ⟨z, w, hw, P, A, hd, hAr, _⟩ := countable_bafa_joint_mask_extensions base hB enum henum
  obtain ⟨r, hG, hExt, hInv, hr⟩ := mask_partner_graph_exists base P A hd hAr
  obtain ⟨J, f, hJ, hc, hs, hcore, hCover, hD, hR, hF, hf, hfi⟩ :=
    invariant_core_graph_hereditary_realization base hB hw P A hd hAr hG hExt hInv enum henum
  have hj : ∀ i, ElementaryMap s s (J i) := fun i => (hJ i).1
  have ho := fun i => (hJ i).2.1
  have hl := fun i => (hJ i).2.2
  let D : MaskSupportedCarrier s w J := ⟨A.domain, hD⟩
  let R : MaskSupportedCarrier s w J := ⟨r, hR⟩
  let F : MaskSupportedCarrier s w J := ⟨f, hF⟩
  obtain ⟨T, hT, hfH, hfiH, hRange⟩ := mask_realization_transitive_range base hj hs D R F hf hfi
  have hp := mask_carrier_pairing base hw J hj
  have hu := mask_carrier_union base J hj ho
  have hpow := mask_carrier_power_of_joint_covers base hj hc hs (fun d => hCover d.val)
  have hsep := mask_carrier_bounded_separation base hw J hj ho
  refine ⟨z, w, hw, P, J, hJ, hc, hs, hcore, hCover,
    hereditary_mask_family base hw P J hj ho hcore,
    mask_carrier_extensional base.extensional J, mask_carrier_empty base hw J hj ho,
    hp, hu, hpow, mask_carrier_infinity base hw J hl, hsep,
    power_bounded_separation_of_bounded hp hu hpow hsep, mask_carrier_not_choice base hw P hj ho hcore,
    D, R, F, T, hd, hr, (mask_graph_iff D R).mpr hG, (mask_graph_extensional_iff D R).mpr hExt,
    hfH, hfiH, hRange, hT, ?_⟩
  intro i l k hl hk
  obtain ⟨hld, hkd, _, _⟩ := partner_graph_rows base P hd hr hl hk
  obtain ⟨L, hlL, _⟩ := hf.1.2 l hld
  obtain ⟨K, hkK, _⟩ := hf.1.2 k hkd
  let LH : MaskSupportedCarrier s w J := ⟨L, (mask_relation_components hF hlL).2⟩
  let KH : MaskSupportedCarrier s w J := ⟨K, (mask_relation_components hF hkK).2⟩
  exact ⟨LH, KH, hlL, hkK, (mask_two_cycle_iff LH KH).mpr
    (partner_decoration_two_cycles base P hd hr hf hfi hl hk hlL hkK)⟩

#print axioms countable_bafa_internal_two_cycle_candidate
end FullBridge
