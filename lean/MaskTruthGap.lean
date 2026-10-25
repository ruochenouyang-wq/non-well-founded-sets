import MaskSeparationTraces
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem mask_no_supported_selector (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hj : ∀ i, ElementaryMap s s (J i)) (ho : ∀ i y, ∃ x, J i x = y)
    (hcore : ∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) :
    ¬ ∃ f : MaskSupportedCarrier s w J,
      ChoiceFunctionCode (maskSupportedMember J)
        ⟨P.family, hereditary_mask_family base hw P J hj ho hcore⟩ f := by
  rintro ⟨f, hf⟩
  exact global_selector_not_mask_supported base hw P J hj ho hcore
    (mask_choice_function_ambient _ f hf) (hereditary_mask_root f.property)

/-- The source has an actual selector for this coded family without source AC.
    The same existential formula is false in the hereditary carrier. -/
theorem mask_selector_truth_gap (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hj : ∀ i, ElementaryMap s s (J i)) (ho : ∀ i y, ∃ x, J i x = y)
    (hcore : ∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) :
    Eval s hasSelectorFormula (fun _ => P.family) ∧
      ¬ Eval (maskSupportedMember J) hasSelectorFormula
        (fun _ => ⟨P.family, hereditary_mask_family base hw P J hj ho hcore⟩) := by
  refine ⟨(eval_hasSelectorFormula s _).mpr (internal_quine_pairs_have_choice base P), ?_⟩
  intro h
  exact mask_no_supported_selector base hw P J hj ho hcore ((eval_hasSelectorFormula _ _).mp h)

theorem mask_inclusion_not_elementary (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hj : ∀ i, ElementaryMap s s (J i)) (ho : ∀ i y, ∃ x, J i x = y)
    (hcore : ∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) :
    ¬ ElementaryMap (maskSupportedMember J) s (fun X => X.val) := by
  intro he
  have hgap := mask_selector_truth_gap base hw P J hj ho hcore
  exact hgap.2 ((he hasSelectorFormula
    (fun _ => ⟨P.family, hereditary_mask_family base hw P J hj ho hcore⟩)).mpr hgap.1)

#print axioms mask_inclusion_not_elementary
end FullBridge
