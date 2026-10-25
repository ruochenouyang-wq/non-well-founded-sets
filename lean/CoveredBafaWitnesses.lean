import MaskCoveredDecorations
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Full fixed-parameter BAFA yields internally covered witnesses whenever
    its hereditary node set is internally covered. -/
theorem mask_bafa_covered_witnesses (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hs : ∀ i x, J i (J i x) = x) (hB : BAFACode (maskSupportedMember J))
    (t a r : MaskSupportedCarrier s w J) (ht : TransitiveCode (maskSupportedMember J) t)
    (hG : GraphCode (maskSupportedMember J) a r) (hE : GraphExtensionalCode (maskSupportedMember J) a r)
    (hEnd : EndExtensionCode (maskSupportedMember J) a r t) (ha : InternalMaskCovered s w J a.val) :
    ∃ T f : MaskSupportedCarrier s w J,
      TransitiveCode (maskSupportedMember J) T ∧ DecorationCode (maskSupportedMember J) a r f ∧
      InjectiveCode (maskSupportedMember J) f ∧ RangeCode (maskSupportedMember J) a f T ∧
      (∀ x, maskSupportedMember J x t → CodedRelation (maskSupportedMember J) f x x) ∧
      InternalMaskCovered s w J f.val ∧ InternalMaskCovered s w J T.val ∧
      ∀ x X, CodedRelation s f.val x X → InternalMaskCovered s w J X := by
  obtain ⟨T, f, hT, hf, hi, hr, hfix⟩ := hB t ht a r hG hE hEnd
  have hfs := (mask_decoration_iff a r f).mp hf
  have hfc := (mask_decoration_covered_iff_domain base hj hs a.property hfs f.property).mpr ha
  have hTc := hereditary_transitive_internal_mask_covered base.pairing base.union
    ((mask_transitive_iff T).mp hT) T.property
  exact ⟨T, f, hT, hf, hi, hr, hfix, hfc, hTc, fun x X hxX =>
    internal_mask_covered_member hTc (((mask_range_iff a f T).mp hr X).mpr
      ⟨x, coded_function_domain hfs.1 hxX, hxX⟩)⟩

/-- The chosen function and its whole transitive range fit into one actual
    jointly coded, mask-fixed hereditary transitive source core. -/
theorem mask_bafa_witnesses_in_joint_core (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ D, TransitiveCode s D ∧ Nonempty (JointMaskDomain s w J D) ∧ Subset s d D)
    (hB : BAFACode (maskSupportedMember J))
    (t a r : MaskSupportedCarrier s w J) (ht : TransitiveCode (maskSupportedMember J) t)
    (hG : GraphCode (maskSupportedMember J) a r) (hE : GraphExtensionalCode (maskSupportedMember J) a r)
    (hEnd : EndExtensionCode (maskSupportedMember J) a r t) (ha : InternalMaskCovered s w J a.val) :
    ∃ T f : MaskSupportedCarrier s w J,
      TransitiveCode (maskSupportedMember J) T ∧ DecorationCode (maskSupportedMember J) a r f ∧
      InjectiveCode (maskSupportedMember J) f ∧ RangeCode (maskSupportedMember J) a f T ∧
      (∀ x, maskSupportedMember J x t → CodedRelation (maskSupportedMember J) f x x) ∧
      ∃ C, TransitiveCode s C ∧ HereditarilyMaskSupported s w J C ∧ InternalMaskCovered s w J C ∧
        (∀ i, J i C = C) ∧ Nonempty (JointMaskDomain s w J C) ∧ s f.val C ∧ s T.val C := by
  obtain ⟨T, f, hT, hf, hi, hr, hfix, hfc, hTc, _⟩ :=
    mask_bafa_covered_witnesses base hj hs hB t a r ht hG hE hEnd ha
  obtain ⟨p, hp⟩ := base.pairing f.val T.val
  obtain ⟨D, hD, ⟨A⟩, hpD⟩ := hCover p
  obtain ⟨C, hm, hCt, hCH, hCc, hfixed, hJ⟩ := joint_internal_mask_core_exists base hw A hD hj hc hs
  exact ⟨T, f, hT, hf, hi, hr, hfix, C, hCt, hCH, hCc, hfixed, hJ,
    (hm f.val).mpr ⟨hpD _ ((hp f.val).mpr (Or.inl rfl)), hfc⟩,
    (hm T.val).mpr ⟨hpD _ ((hp T.val).mpr (Or.inr rfl)), hTc⟩⟩

#print axioms mask_bafa_witnesses_in_joint_core
end FullBridge
