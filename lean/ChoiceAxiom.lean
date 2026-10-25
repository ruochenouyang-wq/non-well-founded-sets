import ModelBridge
namespace FullBridge
universe u
variable {U : Type u}

def ChoiceFunctionCode (s : U → U → Prop) (a f : U) : Prop :=
  FunctionCode s a f ∧ ∀ x, s x a → ∀ y, CodedRelation s f x y → s y x

def ChoiceCode (s : U → U → Prop) : Prop :=
  ∀ a, (∀ x, s x a → ∃ y, s y x) → ∃ f, ChoiceFunctionCode s a f

def choiceFunctionFormula {n} (a f : Fin n) : Formula n :=
  .conj (functionCodeFormula a f)
    (.all (.impl (.member 0 a.succ)
      (.all (.impl (relatedFormula f.succ.succ 1 0) (.member 0 1)))))

theorem eval_choiceFunctionFormula (s : U → U → Prop) {n} (a f : Fin n) (v : Fin n → U) :
    Eval s (choiceFunctionFormula a f) v ↔ ChoiceFunctionCode s (v a) (v f) := by
  simp only [choiceFunctionFormula, Eval, eval_functionCodeFormula, eval_relatedFormula,
    ChoiceFunctionCode, cons_succ]
  rfl

def choiceSentence : Formula 0 :=
  .all (.impl (.all (.impl (.member 0 1) (.ex (.member 0 1))))
    (.ex (choiceFunctionFormula 1 0)))

theorem eval_choiceSentence (s : U → U → Prop) :
    Eval s choiceSentence Fin.elim0 ↔ ChoiceCode s := by
  simp only [choiceSentence, Eval, eval_choiceFunctionFormula, ChoiceCode]
  rfl

theorem choiceFunction_forward_compatible {V : Type u} {s : U → U → Prop}
    {t : V → V → Prop} {q : U → V} (hm : ExactMembers s t q) {a f : U}
    (hf : ChoiceFunctionCode s a f)
    (hc : ∀ x x' y y', s x a → s x' a → q x = q x' →
      CodedRelation s f x y → CodedRelation s f x' y' → q y = q y') :
    ChoiceFunctionCode t (q a) (q f) := by
  refine ⟨functionCode_forward hm hf.1 hc, ?_⟩
  intro X _ Y hXY
  obtain ⟨x, y, hx, hxy, rfl, rfl⟩ := (codedRelation_image hm hf.1.1 X Y).mp hXY
  exact (hm x (q y)).mpr ⟨y, hf.2 x hx y hxy, rfl⟩

#print axioms choiceFunction_forward_compatible
end FullBridge
