import CrossFieldBridge
import CoveredPairChoiceFailure

namespace FullBridge
universe u

theorem bafa_translated_fiber_pair_choice (M : BafaModel.{u}) :
    Eval M.mem (behaviorTranslation fiberPairChoiceSentence) Fin.elim0 :=
  (bridge_sentence_translation M fiberPairChoiceSentence).mpr
    (afa_fiber_pair_choice_sentence M.behaviorQuotient.base M.behaviorQuotient.antiFoundation)

/-- Raw identity choice can fail while its behavior-translated sentence holds.
    The full model is constructed conditionally from a countable BAFA model. -/
theorem countable_bafa_pair_choice_translation_boundary {U : Type u} {s : U → U → Prop}
    (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ M : BafaModel.{u}, ¬ PairChoiceCode M.mem ∧
      ¬ Eval M.mem fiberPairChoiceSentence Fin.elim0 ∧
      Eval M.mem (behaviorTranslation fiberPairChoiceSentence) Fin.elim0 := by
  obtain ⟨M, hpc, hfc, _⟩ := countable_bafa_pair_choice_complete_bridge base hB enum henum
  exact ⟨M, hpc, fun h => hfc (eval_fiberPairChoiceSentence.mp h),
    bafa_translated_fiber_pair_choice M⟩

end FullBridge
