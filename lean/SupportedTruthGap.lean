import SupportedRelativePower
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- One parameter: the family for which an internal selector is requested. -/
def hasSelectorFormula : Formula 1 := .ex (choiceFunctionFormula 1 0)

theorem eval_hasSelectorFormula (s : U → U → Prop) (v : Fin 1 → U) :
    Eval s hasSelectorFormula v ↔ ∃ f, ChoiceFunctionCode s (v 0) f := by
  simp only [hasSelectorFormula, Eval, eval_choiceFunctionFormula]
  rfl

theorem pair_sequence_no_supported_selector {F : U} (S : PairSwapSequence s F) :
    ¬ ∃ f : SupportedCarrier s S.map,
      ChoiceFunctionCode (supportedMember S.map)
        ⟨F, pair_sequence_family_hereditarily_supported S⟩ f := by
  rintro ⟨f, hf⟩
  have hsource := supported_choice_function_ambient _ f hf
  obtain ⟨N, hN⟩ := hereditary_support_root f.property
  exact (S.action N).moves_choice f.val hsource (hN N (Nat.le_refl N))

/-- A specific formula is true in the source and false in the subtype,
    without assuming Choice for the source universe. -/
theorem pair_sequence_selector_truth_gap {F f : U} (S : PairSwapSequence s F)
    (hf : ChoiceFunctionCode s F f) :
    Eval s hasSelectorFormula (fun _ => F) ∧
      ¬ Eval (supportedMember S.map) hasSelectorFormula
        (fun _ => ⟨F, pair_sequence_family_hereditarily_supported S⟩) := by
  refine ⟨(eval_hasSelectorFormula s _).mpr ⟨f, hf⟩, ?_⟩
  intro h
  exact pair_sequence_no_supported_selector S ((eval_hasSelectorFormula _ _).mp h)

theorem pair_sequence_inclusion_not_elementary {F f : U} (S : PairSwapSequence s F)
    (hf : ChoiceFunctionCode s F f) :
    ¬ ElementaryMap (supportedMember (s := s) S.map) s (fun X => X.val) := by
  intro he
  have hgap := pair_sequence_selector_truth_gap S hf
  exact hgap.2 ((he hasSelectorFormula
    (fun _ => ⟨F, pair_sequence_family_hereditarily_supported S⟩)).mpr hgap.1)

/-- The commuting invariant candidate really exhibits the semantic gap;
    trace existence remains an explicit, equivalent obligation for each
    of full Separation and relative PowerSet. -/
theorem countable_bafa_supported_truth_and_trace_criteria
    (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ F, ∃ S : PairSwapSequence s F,
      (∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) ∧
      (∃ f, ChoiceFunctionCode s F f) ∧
      (Eval s hasSelectorFormula (fun _ => F) ∧
        ¬ Eval (supportedMember S.map) hasSelectorFormula
          (fun _ => ⟨F, pair_sequence_family_hereditarily_supported S⟩)) ∧
      ¬ ElementaryMap (supportedMember (s := s) S.map) s (fun X => X.val) ∧
      (Separation (supportedMember (s := s) S.map) ↔ SupportedSeparationTraces s S.map) ∧
      (PowerSet (supportedMember (s := s) S.map) ↔ SupportedPowerTraces s S.map) := by
  obtain ⟨F, S, f, hf⟩ := bafa_pair_sequence_with_ambient_choice base hB enum henum
  obtain ⟨T, _, _, hc⟩ := pair_sequence_commuting_extension base hB enum henum S
  exact ⟨F, T, hc, ⟨f, hf⟩, pair_sequence_selector_truth_gap T hf,
    pair_sequence_inclusion_not_elementary T hf,
    supported_full_separation_iff_traces base T hc, supported_power_iff_traces base T hc⟩

#print axioms countable_bafa_supported_truth_and_trace_criteria
end FullBridge
