import ChoiceTransfer
namespace FullBridge
universe u

structure BafaChoiceModel extends BafaModel.{u} where
  choice : ChoiceCode mem

structure AfaChoiceModel extends AfaModel.{u} where
  choice : ChoiceCode mem

def BafaChoiceModel.behaviorQuotient (M : BafaChoiceModel.{u}) : AfaChoiceModel.{u} where
  toAfaModel := M.toBafaModel.behaviorQuotient
  choice := internal_choice M.base M.choice

theorem bafa_to_afa_choice_model_existence :
    Nonempty BafaChoiceModel.{u} → Nonempty AfaChoiceModel.{u} := by
  rintro ⟨M⟩
  exact ⟨M.behaviorQuotient⟩

theorem bridge_translated_choice (M : BafaChoiceModel.{u}) :
    Eval M.mem (Formula.translate (internalInterpretation M.base).equalFormula
      (internalInterpretation M.base).memberFormula choiceSentence) Fin.elim0 :=
  (bridge_sentence_translation M.toBafaModel choiceSentence).mpr
    ((eval_choiceSentence M.behaviorQuotient.mem).mpr M.behaviorQuotient.choice)

#print axioms bafa_to_afa_choice_model_existence
end FullBridge
