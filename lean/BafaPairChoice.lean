import PairChoicePrinciples

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Internal injective images preserve exactly two elements. No orientation
    function on a whole family of pairs is part of the input. -/
theorem coded_image_two_element {d i x c : U}
    (hi : FunctionCode s d i) (hinj : InjectiveCode s i)
    (hxd : Subset s x d) (hx : TwoElement s x) (hc : CodedImageSet s i x c) :
    TwoElement s c := by
  obtain ⟨y, z, hyz, hp⟩ := hx
  have hyx := (hp y).mpr (Or.inl rfl)
  have hzx := (hp z).mpr (Or.inr rfl)
  obtain ⟨v, hyv, huv⟩ := hi.2 y (hxd y hyx)
  obtain ⟨w, hzw, huw⟩ := hi.2 z (hxd z hzx)
  refine ⟨v, w, ?_, ?_⟩
  · intro hvw
    exact hyz (hinj y z w (hvw ▸ hyv) hzw)
  · intro t
    constructor
    · intro ht
      obtain ⟨b, hbx, hbt⟩ := (hc t).mp ht
      rcases (hp b).mp hbx with hby | hbz
      · subst b
        exact Or.inl (huv t hbt)
      · subst b
        exact Or.inr (huw t hbt)
    · intro ht
      rcases ht with htv | htw
      · subst t
        exact (hc v).mpr ⟨y, hyx, hyv⟩
      · subst t
        exact (hc w).mpr ⟨z, hzx, hzw⟩

/-- One internal injection relabels the union of an arbitrary pair family by
    distinct self-singletons. Each image pair still has exactly two elements. -/
theorem bafa_pair_family_into_quines (base : BaseCollection s) (hB : BAFACode s)
    (a : U) (ha : ∀ x, s x a → TwoElement s x) :
    ∃ b i, InjectiveCode s i ∧
      (∀ c, s c b ↔ ∃ x, s x a ∧ CodedImageSet s i x c) ∧
      (∀ c, s c b → TwoElement s c ∧ (∀ v, s v c → SelfSingleton s v)) := by
  obtain ⟨d, hd⟩ := base.union a
  obtain ⟨i, hi, hinj, hself⟩ := bafa_selfSingleton_family base hB d
  obtain ⟨b, hb⟩ := coded_image_set_family base a i
  refine ⟨b, i, hinj, hb, ?_⟩
  intro c hcb
  obtain ⟨x, hxa, hcx⟩ := (hb c).mp hcb
  have hxd : Subset s x d := fun y hy => (hd y).mpr ⟨x, hxa, hy⟩
  refine ⟨coded_image_two_element hi hinj hxd (ha x hxa) hcx, ?_⟩
  intro v hvc
  obtain ⟨y, hyx, hyv⟩ := (hcx v).mp hvc
  exact hself y v (hxd y hyx) hyv

theorem bafa_quine_pair_choice_implies_pair_choice (base : BaseCollection s)
    (hB : BAFACode s) (hQC : QuinePairChoiceCode s) : PairChoiceCode s := by
  intro a ha
  obtain ⟨b, i, hinj, hb, hq⟩ := bafa_pair_family_into_quines base hB a ha
  obtain ⟨k, hk⟩ := hQC b hq
  exact choice_transports_injection base hinj hb hk

theorem bafa_fiber_pair_choice_iff_pair_choice (base : BaseCollection s)
    (hB : BAFACode s) : FiberPairChoiceCode s ↔ PairChoiceCode s :=
  ⟨fun h => bafa_quine_pair_choice_implies_pair_choice base hB
    (fiber_pair_choice_implies_quine_pair_choice base h),
    pair_choice_implies_fiber_pair_choice⟩

theorem bafa_quine_pair_choice_iff_pair_choice (base : BaseCollection s)
    (hB : BAFACode s) : QuinePairChoiceCode s ↔ PairChoiceCode s :=
  ⟨bafa_quine_pair_choice_implies_pair_choice base hB,
    fun h => fiber_pair_choice_implies_quine_pair_choice base
      (pair_choice_implies_fiber_pair_choice h)⟩

theorem bafa_fiber_pair_choice_sentence_equiv (base : BaseCollection s)
    (hB : BAFACode s) :
    Eval s fiberPairChoiceSentence Fin.elim0 ↔ Eval s pairChoiceSentence Fin.elim0 := by
  rw [eval_fiberPairChoiceSentence, eval_pairChoiceSentence]
  exact bafa_fiber_pair_choice_iff_pair_choice base hB

theorem bafa_quine_pair_choice_sentence_equiv (base : BaseCollection s)
    (hB : BAFACode s) :
    Eval s quinePairChoiceSentence Fin.elim0 ↔ Eval s pairChoiceSentence Fin.elim0 := by
  rw [eval_quinePairChoiceSentence, eval_pairChoiceSentence]
  exact bafa_quine_pair_choice_iff_pair_choice base hB

end FullBridge
