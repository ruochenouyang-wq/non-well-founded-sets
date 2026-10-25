import DefinableKernel

namespace FullBridge
universe u

namespace Formula
def disj {n} (p q : Formula n) : Formula n := .impl (.impl p .bottom) q
def iffF {n} (p q : Formula n) : Formula n := .conj (.impl p q) (.impl q p)
end Formula

theorem eval_disj {U : Type u} (s : U → U → Prop) {n} (p q : Formula n) (e : Fin n → U) :
    Eval s (p.disj q) e ↔ Eval s p e ∨ Eval s q e := by
  classical
  change ((Eval s p e → False) → Eval s q e) ↔ _
  by_cases hp : Eval s p e <;> simp [hp]

theorem eval_iffF {U : Type u} (s : U → U → Prop) {n} (p q : Formula n) (e : Fin n → U) :
    Eval s (p.iffF q) e ↔ (Eval s p e ↔ Eval s q e) := by
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

def IsPair {U : Type u} (s : U → U → Prop) (p x y : U) : Prop :=
  ∀ z, s z p ↔ z = x ∨ z = y

def pairFormula {n} (p x y : Fin n) : Formula n :=
  .all ((Formula.member 0 p.succ).iffF ((Formula.equal 0 x.succ).disj (.equal 0 y.succ)))

theorem eval_pairFormula {U : Type u} (s : U → U → Prop) {n}
    (p x y : Fin n) (e : Fin n → U) :
    Eval s (pairFormula p x y) e ↔ IsPair s (e p) (e x) (e y) := by
  simp only [pairFormula, Eval, eval_iffF, eval_disj, cons_zero, cons_succ, IsPair]

def IsOrderedPair {U : Type u} (s : U → U → Prop) (p x y : U) : Prop :=
  ∃ a b, IsPair s a x x ∧ IsPair s b x y ∧ IsPair s p a b

def orderedPairFormula {n} (p x y : Fin n) : Formula n :=
  .ex (.ex (.conj (pairFormula 1 x.succ.succ x.succ.succ)
    (.conj (pairFormula 0 x.succ.succ y.succ.succ) (pairFormula p.succ.succ 1 0))))

theorem eval_orderedPairFormula {U : Type u} (s : U → U → Prop) {n}
    (p x y : Fin n) (e : Fin n → U) :
    Eval s (orderedPairFormula p x y) e ↔ IsOrderedPair s (e p) (e x) (e y) := by
  simp only [orderedPairFormula, Eval, eval_pairFormula, cons_zero, cons_succ, IsOrderedPair]
  rfl

def CodedRelation {U : Type u} (s : U → U → Prop) (r x y : U) : Prop :=
  ∃ p, s p r ∧ IsOrderedPair s p x y

def relatedFormula {n} (r x y : Fin n) : Formula n :=
  .ex (.conj (.member 0 r.succ) (orderedPairFormula 0 x.succ y.succ))

theorem eval_relatedFormula {U : Type u} (s : U → U → Prop) {n}
    (r x y : Fin n) (e : Fin n → U) :
    Eval s (relatedFormula r x y) e ↔ CodedRelation s (e r) (e x) (e y) := by
  simp only [relatedFormula, Eval, eval_orderedPairFormula, cons_zero, cons_succ, CodedRelation]

def bisimFormula {n} (r : Fin n) : Formula n :=
  .all (.all (.impl (relatedFormula r.succ.succ 1 0)
    (.conj
      (.all (.impl (.member 0 2) (.ex (.conj (.member 0 2)
        (relatedFormula r.succ.succ.succ.succ 1 0)))))
      (.all (.impl (.member 0 1) (.ex (.conj (.member 0 3)
        (relatedFormula r.succ.succ.succ.succ 0 1))))))))

theorem eval_bisimFormula {U : Type u} (s : U → U → Prop) {n}
    (r : Fin n) (e : Fin n → U) :
    Eval s (bisimFormula r) e ↔ Bisimulation s (CodedRelation s (e r)) := by
  simp only [bisimFormula, Eval, eval_relatedFormula, cons_zero, cons_succ, Bisimulation]
  rfl

def CodedBehavior {U : Type u} (s : U → U → Prop) (x y : U) : Prop :=
  ∃ r, Bisimulation s (CodedRelation s r) ∧ CodedRelation s r x y

def codedBehaviorFormula {n} (x y : Fin n) : Formula n :=
  .ex (.conj (bisimFormula 0) (relatedFormula 0 x.succ y.succ))

theorem eval_codedBehaviorFormula {U : Type u} (s : U → U → Prop) {n}
    (x y : Fin n) (e : Fin n → U) :
    Eval s (codedBehaviorFormula x y) e ↔ CodedBehavior s (e x) (e y) := by
  simp only [codedBehaviorFormula, Eval, eval_bisimFormula, eval_relatedFormula,
    cons_zero, cons_succ, CodedBehavior]

theorem codedBehavior_implies_behavior {U : Type u} {s : U → U → Prop} {x y : U}
    (h : CodedBehavior s x y) : Behavior s x y := by
  obtain ⟨r, hr, hxy⟩ := h
  exact ⟨CodedRelation s r, hr, hxy⟩

#print axioms eval_codedBehaviorFormula
end FullBridge
