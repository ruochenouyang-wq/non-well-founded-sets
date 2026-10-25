import InternalExtensionality

namespace FullBridge
universe u
variable {U : Type u}

def GraphCode (s : U → U → Prop) (a r : U) : Prop :=
  ∀ p, s p r → ∃ x y, s x a ∧ s y a ∧ IsOrderedPair s p x y

def FunctionCode (s : U → U → Prop) (a f : U) : Prop :=
  (∀ p, s p f → ∃ x y, s x a ∧ IsOrderedPair s p x y) ∧
  ∀ x, s x a → ∃ y, CodedRelation s f x y ∧ ∀ z, CodedRelation s f x z → z = y

def DecorationCode (s : U → U → Prop) (a r f : U) : Prop :=
  FunctionCode s a f ∧ ∀ x, s x a → ∀ v, CodedRelation s f x v →
    ∀ w, s w v ↔ ∃ y, s y a ∧ CodedRelation s r x y ∧ CodedRelation s f y w

def AFACode (s : U → U → Prop) : Prop :=
  ∀ a r, GraphCode s a r → ∃ f, DecorationCode s a r f ∧
    ∀ g, DecorationCode s a r g → g = f

def graphCodeFormula {n} (a r : Fin n) : Formula n :=
  .all (.impl (.member 0 r.succ) (.ex (.ex (.conj (.member 1 a.succ.succ.succ)
    (.conj (.member 0 a.succ.succ.succ) (orderedPairFormula 2 1 0))))))

theorem eval_graphCodeFormula (s : U → U → Prop) {n} (a r : Fin n) (e : Fin n → U) :
    Eval s (graphCodeFormula a r) e ↔ GraphCode s (e a) (e r) := by
  simp only [graphCodeFormula, Eval, eval_orderedPairFormula, GraphCode, cons_zero, cons_succ]
  rfl

def functionCodeFormula {n} (a f : Fin n) : Formula n :=
  .conj
    (.all (.impl (.member 0 f.succ) (.ex (.ex (.conj (.member 1 a.succ.succ.succ)
      (orderedPairFormula 2 1 0))))))
    (.all (.impl (.member 0 a.succ) (.ex (.conj (relatedFormula f.succ.succ 1 0)
      (.all (.impl (relatedFormula f.succ.succ.succ 2 0) (.equal 0 1)))))))

theorem eval_functionCodeFormula (s : U → U → Prop) {n} (a f : Fin n) (e : Fin n → U) :
    Eval s (functionCodeFormula a f) e ↔ FunctionCode s (e a) (e f) := by
  simp only [functionCodeFormula, Eval, eval_orderedPairFormula, eval_relatedFormula,
    FunctionCode, cons_zero, cons_succ]
  rfl

def decorationCodeFormula {n} (a r f : Fin n) : Formula n :=
  .conj (functionCodeFormula a f)
    (.all (.impl (.member 0 a.succ)
      (.all (.impl (relatedFormula f.succ.succ 1 0)
        (.all ((Formula.member 0 1).iffF
          (.ex (.conj (.member 0 a.succ.succ.succ.succ)
            (.conj (relatedFormula r.succ.succ.succ.succ 3 0)
              (relatedFormula f.succ.succ.succ.succ 0 1))))))))))

theorem eval_decorationCodeFormula (s : U → U → Prop) {n}
    (a r f : Fin n) (e : Fin n → U) :
    Eval s (decorationCodeFormula a r f) e ↔ DecorationCode s (e a) (e r) (e f) := by
  simp only [decorationCodeFormula, Eval, eval_functionCodeFormula, eval_relatedFormula,
    eval_iffF, DecorationCode, cons_zero, cons_succ]
  rfl

def afaSentence : Formula 0 :=
  .all (.all (.impl (graphCodeFormula 1 0)
    (.ex (.conj (decorationCodeFormula 2 1 0)
      (.all (.impl (decorationCodeFormula 3 2 0) (.equal 0 1)))))))

theorem eval_afaSentence (s : U → U → Prop) :
    Eval s afaSentence Fin.elim0 ↔ AFACode s := by
  simp only [afaSentence, Eval, eval_graphCodeFormula, eval_decorationCodeFormula, AFACode]
  rfl

#print axioms eval_afaSentence
end FullBridge
