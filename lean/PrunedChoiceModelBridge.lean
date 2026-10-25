import PrunedChoiceTransfer
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def AfaChoiceModel.prunedBafa (M : AfaChoiceModel.{u}) (b : M.Carrier)
    (hb : SelfSingleton M.mem b) : BafaChoiceModel.{u} where
  toBafaModel := M.toAfaModel.prunedBafa b hb
  choice := pruned_quotient_choice M.base M.choice ((hb b).mpr rfl)

theorem afa_to_bafa_choice_model_existence :
    Nonempty AfaChoiceModel.{u} → Nonempty BafaChoiceModel.{u} := by
  rintro ⟨M⟩
  obtain ⟨b, hb⟩ := solvability_selfSingleton_exists M.base
    (fixed_solvability_implies_solvability M.base (afa_fixed_graph_solvability M.base M.antiFoundation))
  exact ⟨M.prunedBafa b hb⟩

theorem bafa_afa_choice_model_existence_iff :
    Nonempty BafaChoiceModel.{u} ↔ Nonempty AfaChoiceModel.{u} :=
  ⟨bafa_to_afa_choice_model_existence, afa_to_bafa_choice_model_existence⟩

theorem pruned_bridge_translated_choice (base : BaseCollection s) (hAC : ChoiceCode s)
    {b : U} (hbb : s b b) :
    Eval s (prunedTheoryTranslation choiceSentence) (cons b Fin.elim0) := by
  apply (pruned_theory_formula_translation base b choiceSentence Fin.elim0).mpr
  have he : (fun i : Fin 0 => prunedCode base b (Fin.elim0 i)) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [he]
  exact (eval_choiceSentence _).mpr (pruned_quotient_choice base hAC hbb)

theorem retained_pruned_choice (base : BaseCollection s) (hAC : ChoiceCode s)
    {b : U} (hbb : s b b) : ChoiceCode (retainedPrunedMember base b) := by
  apply (eval_choiceSentence _).mp
  apply (retained_pruned_formula_semantics base b choiceSentence Fin.elim0).mpr
  have he : (fun i : Fin 0 => retainedPrunedToFull base b (Fin.elim0 i)) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [he]
  exact (eval_choiceSentence _).mpr (pruned_quotient_choice base hAC hbb)

#print axioms bafa_afa_choice_model_existence_iff
#print axioms retained_pruned_choice
end FullBridge
