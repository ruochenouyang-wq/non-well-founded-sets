import BafaPairChoice
import AfaInternalCoinduction

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem empty_family_choice_function (base : BaseCollection s) {a : U}
    (ha : ∀ x, ¬ s x a) : ∃ f, ChoiceFunctionCode s a f := by
  obtain ⟨e, he⟩ := base.empty
  exact ⟨e, ⟨fun p hp => (he p hp).elim, fun x hx => (ha x hx).elim⟩,
    fun x hx => (ha x hx).elim⟩

theorem afa_no_homogeneous_pair (base : BaseCollection s) (hA : AFACode s)
    {c : U} (hc : TwoElement s c) : ¬ BehaviorHomogeneous s c := by
  obtain ⟨x, y, hne, hp⟩ := hc
  intro hH
  exact hne ((afa_internal_behavior_iff_equal base hA x y).mp
    (hH x y ((hp x).mpr (Or.inl rfl)) ((hp y).mpr (Or.inr rfl))))

theorem afa_fiber_pair_choice (base : BaseCollection s) (hA : AFACode s) :
    FiberPairChoiceCode s := by
  intro a ha
  apply empty_family_choice_function base
  intro c hc
  exact afa_no_homogeneous_pair base hA (ha c hc).1 (ha c hc).2

theorem afa_quine_pair_choice (base : BaseCollection s) (hA : AFACode s) :
    QuinePairChoiceCode s :=
  fiber_pair_choice_implies_quine_pair_choice base (afa_fiber_pair_choice base hA)

theorem afa_fiber_pair_choice_sentence (base : BaseCollection s) (hA : AFACode s) :
    Eval s fiberPairChoiceSentence Fin.elim0 :=
  eval_fiberPairChoiceSentence.mpr (afa_fiber_pair_choice base hA)

theorem afa_quine_pair_choice_sentence (base : BaseCollection s) (hA : AFACode s) :
    Eval s quinePairChoiceSentence Fin.elim0 :=
  eval_quinePairChoiceSentence.mpr (afa_quine_pair_choice base hA)

end FullBridge
