import BoffaAxiom

namespace FullBridge
universe u
variable {U : Type u}

def transitiveFormula {n} (a : Fin n) : Formula n :=
  .all (.impl (.member 0 a.succ) (.all (.impl (.member 0 1) (.member 0 a.succ.succ))))

theorem eval_transitiveFormula (s : U → U → Prop) {n} (a : Fin n) (e : Fin n → U) :
    Eval s (transitiveFormula a) e ↔ TransitiveCode s (e a) := by
  simp only [transitiveFormula, Eval, TransitiveCode, cons_zero, cons_succ]
  rfl

def graphExtensionalFormula {n} (a r : Fin n) : Formula n :=
  .all (.impl (.member 0 a.succ) (.all (.impl (.member 0 a.succ.succ)
    (.impl (.all (.impl (.member 0 a.succ.succ.succ)
      ((relatedFormula r.succ.succ.succ 2 0).iffF
        (relatedFormula r.succ.succ.succ 1 0)))) (.equal 1 0)))))

theorem eval_graphExtensionalFormula (s : U → U → Prop) {n}
    (a r : Fin n) (e : Fin n → U) :
    Eval s (graphExtensionalFormula a r) e ↔ GraphExtensionalCode s (e a) (e r) := by
  simp only [graphExtensionalFormula, Eval, eval_relatedFormula, eval_iffF,
    GraphExtensionalCode, cons_zero, cons_succ]
  rfl

def injectiveFormula {n} (f : Fin n) : Formula n :=
  .all (.all (.all (.impl (relatedFormula f.succ.succ.succ 2 0)
    (.impl (relatedFormula f.succ.succ.succ 1 0) (.equal 2 1)))))

theorem eval_injectiveFormula (s : U → U → Prop) {n} (f : Fin n) (e : Fin n → U) :
    Eval s (injectiveFormula f) e ↔ InjectiveCode s (e f) := by
  simp only [injectiveFormula, Eval, eval_relatedFormula, InjectiveCode, cons_succ]
  rfl

def rangeFormula {n} (a f t : Fin n) : Formula n :=
  .all ((Formula.member 0 t.succ).iffF
    (.ex (.conj (.member 0 a.succ.succ) (relatedFormula f.succ.succ 0 1))))

theorem eval_rangeFormula (s : U → U → Prop) {n} (a f t : Fin n) (e : Fin n → U) :
    Eval s (rangeFormula a f t) e ↔ RangeCode s (e a) (e f) (e t) := by
  simp only [rangeFormula, Eval, eval_iffF, eval_relatedFormula, RangeCode, cons_zero, cons_succ]
  rfl

def endExtensionFormula {n} (a r t : Fin n) : Formula n :=
  .conj (.all (.impl (.member 0 t.succ) (.member 0 a.succ)))
    (.all (.impl (.member 0 t.succ) (.all
      ((relatedFormula r.succ.succ 1 0).iffF (.member 0 1)))))

theorem eval_endExtensionFormula (s : U → U → Prop) {n} (a r t : Fin n) (e : Fin n → U) :
    Eval s (endExtensionFormula a r t) e ↔ EndExtensionCode s (e a) (e r) (e t) := by
  simp only [endExtensionFormula, Eval, eval_iffF, eval_relatedFormula, EndExtensionCode,
    Subset, cons_zero, cons_succ]
  rfl

def boffaConclusionFormula {n} (t₀ a r t f : Fin n) : Formula n :=
  .conj (transitiveFormula t) (.conj (decorationCodeFormula a r f)
    (.conj (injectiveFormula f) (.conj (rangeFormula a f t)
      (.all (.impl (.member 0 t₀.succ) (relatedFormula f.succ 0 0))))))

theorem eval_boffaConclusionFormula (s : U → U → Prop) {n}
    (t₀ a r t f : Fin n) (e : Fin n → U) :
    Eval s (boffaConclusionFormula t₀ a r t f) e ↔
      TransitiveCode s (e t) ∧ DecorationCode s (e a) (e r) (e f) ∧
        InjectiveCode s (e f) ∧ RangeCode s (e a) (e f) (e t) ∧
          ∀ x, s x (e t₀) → CodedRelation s (e f) x x := by
  simp only [boffaConclusionFormula, Eval, eval_transitiveFormula, eval_decorationCodeFormula,
    eval_injectiveFormula, eval_rangeFormula, eval_relatedFormula, cons_zero, cons_succ]

def bafaSentence : Formula 0 :=
  .all (.impl (transitiveFormula 0)
    (.all (.all (.impl (graphCodeFormula 1 0)
      (.impl (graphExtensionalFormula 1 0)
        (.impl (endExtensionFormula 1 0 2)
          (.ex (.ex (boffaConclusionFormula 4 3 2 1 0)))))))))

theorem eval_bafaSentence (s : U → U → Prop) :
    Eval s bafaSentence Fin.elim0 ↔ BAFACode s := by
  simp only [bafaSentence, Eval, eval_transitiveFormula, eval_graphCodeFormula,
    eval_graphExtensionalFormula, eval_endExtensionFormula, eval_boffaConclusionFormula, BAFACode]
  rfl

#print axioms eval_bafaSentence
end FullBridge
