import BafaFiberChoice

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Exactly two members; the family of these sets may be arbitrarily large
    internally, and is supplied without an orientation of each pair. -/
def TwoElement (s : U → U → Prop) (c : U) : Prop :=
  ∃ x y, x ≠ y ∧ IsPair s c x y

def PairChoiceCode (s : U → U → Prop) : Prop :=
  ∀ a, (∀ c, s c a → TwoElement s c) → ∃ f, ChoiceFunctionCode s a f

def FiberPairChoiceCode (s : U → U → Prop) : Prop :=
  ∀ a, (∀ c, s c a → TwoElement s c ∧ BehaviorHomogeneous s c) →
    ∃ f, ChoiceFunctionCode s a f

def QuinePairChoiceCode (s : U → U → Prop) : Prop :=
  ∀ a, (∀ c, s c a → TwoElement s c ∧ (∀ x, s x c → SelfSingleton s x)) →
    ∃ f, ChoiceFunctionCode s a f

def twoElementFormula {n} (c : Fin n) : Formula n :=
  .ex (.ex (.conj (.impl (.equal 1 0) .bottom) (pairFormula c.succ.succ 1 0)))

def selfSingletonFormula {n} (x : Fin n) : Formula n :=
  .all ((Formula.member 0 x.succ).iffF (.equal 0 x.succ))

def quineMembersFormula {n} (c : Fin n) : Formula n :=
  .all (.impl (.member 0 c.succ) (selfSingletonFormula 0))

def pairChoiceSentence : Formula 0 :=
  .all (.impl (.all (.impl (.member 0 1) (twoElementFormula 0)))
    (.ex (choiceFunctionFormula 1 0)))

def fiberPairChoiceSentence : Formula 0 :=
  .all (.impl (.all (.impl (.member 0 1)
    (.conj (twoElementFormula 0) (behaviorHomogeneousFormula 0))))
    (.ex (choiceFunctionFormula 1 0)))

def quinePairChoiceSentence : Formula 0 :=
  .all (.impl (.all (.impl (.member 0 1)
    (.conj (twoElementFormula 0) (quineMembersFormula 0))))
    (.ex (choiceFunctionFormula 1 0)))

theorem eval_twoElementFormula {n} (c : Fin n) (e : Fin n → U) :
    Eval s (twoElementFormula c) e ↔ TwoElement s (e c) := by
  simp only [twoElementFormula, Eval, eval_pairFormula, TwoElement, cons_zero, cons_succ]
  rfl

theorem eval_selfSingletonFormula {n} (x : Fin n) (e : Fin n → U) :
    Eval s (selfSingletonFormula x) e ↔ SelfSingleton s (e x) := by
  simp only [selfSingletonFormula, Eval, eval_iffF, SelfSingleton, cons_zero, cons_succ]

theorem eval_quineMembersFormula {n} (c : Fin n) (e : Fin n → U) :
    Eval s (quineMembersFormula c) e ↔ ∀ x, s x (e c) → SelfSingleton s x := by
  simp only [quineMembersFormula, Eval, eval_selfSingletonFormula, cons_zero, cons_succ]

theorem eval_pairChoiceSentence :
    Eval s pairChoiceSentence Fin.elim0 ↔ PairChoiceCode s := by
  simp only [pairChoiceSentence, Eval, eval_twoElementFormula,
    eval_choiceFunctionFormula, PairChoiceCode, cons_zero]
  rfl

theorem eval_fiberPairChoiceSentence :
    Eval s fiberPairChoiceSentence Fin.elim0 ↔ FiberPairChoiceCode s := by
  simp only [fiberPairChoiceSentence, Eval, eval_twoElementFormula,
    eval_behaviorHomogeneousFormula, eval_choiceFunctionFormula,
    FiberPairChoiceCode, cons_zero]
  rfl

theorem eval_quinePairChoiceSentence :
    Eval s quinePairChoiceSentence Fin.elim0 ↔ QuinePairChoiceCode s := by
  simp only [quinePairChoiceSentence, Eval, eval_twoElementFormula,
    eval_quineMembersFormula, eval_choiceFunctionFormula,
    QuinePairChoiceCode, cons_zero]
  rfl

theorem two_element_nonempty {c : U} (hc : TwoElement s c) : ∃ x, s x c := by
  obtain ⟨x, y, _, hp⟩ := hc
  exact ⟨x, (hp x).mpr (Or.inl rfl)⟩

theorem choice_implies_pair_choice (hAC : ChoiceCode s) : PairChoiceCode s := by
  intro a ha
  exact hAC a (fun c hc => two_element_nonempty (ha c hc))

theorem pair_choice_implies_fiber_pair_choice (hPC : PairChoiceCode s) :
    FiberPairChoiceCode s := fun a ha => hPC a (fun c hc => (ha c hc).1)

theorem fiber_choice_implies_fiber_pair_choice (hFC : FiberChoiceCode s) :
    FiberPairChoiceCode s := by
  intro a ha
  exact hFC a (fun c hc => ⟨two_element_nonempty (ha c hc).1, (ha c hc).2⟩)

theorem quine_members_behavior_homogeneous (base : BaseCollection s) {c : U}
    (hQ : ∀ x, s x c → SelfSingleton s x) : BehaviorHomogeneous s c := by
  intro x y hx hy
  exact (internal_code_eq base x y).mp (selfSingleton_same_code base (hQ x hx) (hQ y hy))

theorem fiber_pair_choice_implies_quine_pair_choice (base : BaseCollection s)
    (hFC : FiberPairChoiceCode s) : QuinePairChoiceCode s := by
  intro a ha
  exact hFC a (fun c hc => ⟨(ha c hc).1, quine_members_behavior_homogeneous base (ha c hc).2⟩)

end FullBridge
