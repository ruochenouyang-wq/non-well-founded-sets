import GloballyJointMaskActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Both membership-bounded and subset-bounded quantifiers. The subset
    quantifiers range over the current structure, not over external subsets. -/
inductive PowerBoundedFormula : Nat → Type where
  | equal {n} : Fin n → Fin n → PowerBoundedFormula n
  | member {n} : Fin n → Fin n → PowerBoundedFormula n
  | bottom {n} : PowerBoundedFormula n
  | conj {n} : PowerBoundedFormula n → PowerBoundedFormula n → PowerBoundedFormula n
  | impl {n} : PowerBoundedFormula n → PowerBoundedFormula n → PowerBoundedFormula n
  | exMem {n} : Fin n → PowerBoundedFormula (n+1) → PowerBoundedFormula n
  | allMem {n} : Fin n → PowerBoundedFormula (n+1) → PowerBoundedFormula n
  | exSubset {n} : Fin n → PowerBoundedFormula (n+1) → PowerBoundedFormula n
  | allSubset {n} : Fin n → PowerBoundedFormula (n+1) → PowerBoundedFormula n

def PowerBoundedEval (s : U → U → Prop) : {n : Nat} → PowerBoundedFormula n → (Fin n → U) → Prop
  | _, .equal i j, v => v i = v j
  | _, .member i j, v => s (v i) (v j)
  | _, .bottom, _ => False
  | _, .conj p q, v => PowerBoundedEval s p v ∧ PowerBoundedEval s q v
  | _, .impl p q, v => PowerBoundedEval s p v → PowerBoundedEval s q v
  | _, .exMem i p, v => ∃ x, s x (v i) ∧ PowerBoundedEval s p (cons x v)
  | _, .allMem i p, v => ∀ x, s x (v i) → PowerBoundedEval s p (cons x v)
  | _, .exSubset i p, v => ∃ x, Subset s x (v i) ∧ PowerBoundedEval s p (cons x v)
  | _, .allSubset i p, v => ∀ x, Subset s x (v i) → PowerBoundedEval s p (cons x v)

def powerSubsetFormula {n} (i j : Fin n) : Formula n :=
  .all (.impl (.member 0 i.succ) (.member 0 j.succ))

theorem eval_powerSubsetFormula {n} (i j : Fin n) (v : Fin n → U) :
    Eval s (powerSubsetFormula i j) v ↔ Subset s (v i) (v j) := by rfl

def PowerBoundedFormula.toFormula : {n : Nat} → PowerBoundedFormula n → Formula n
  | _, .equal i j => .equal i j
  | _, .member i j => .member i j
  | _, .bottom => .bottom
  | _, .conj p q => .conj p.toFormula q.toFormula
  | _, .impl p q => .impl p.toFormula q.toFormula
  | _, .exMem i p => .ex (.conj (.member 0 i.succ) p.toFormula)
  | _, .allMem i p => .all (.impl (.member 0 i.succ) p.toFormula)
  | _, .exSubset i p => .ex (.conj (powerSubsetFormula 0 i.succ) p.toFormula)
  | _, .allSubset i p => .all (.impl (powerSubsetFormula 0 i.succ) p.toFormula)

theorem power_bounded_eval_toFormula {n} (p : PowerBoundedFormula n) (v : Fin n → U) :
    Eval s p.toFormula v ↔ PowerBoundedEval s p v := by
  induction p with
  | equal => rfl
  | member => rfl
  | bottom => rfl
  | conj p q hp hq => exact and_congr (hp v) (hq v)
  | impl p q hp hq => exact imp_congr (hp v) (hq v)
  | exMem i p hp =>
    simp only [PowerBoundedFormula.toFormula, Eval, cons_zero, cons_succ, PowerBoundedEval, hp]
  | allMem i p hp =>
    simp only [PowerBoundedFormula.toFormula, Eval, cons_zero, cons_succ, PowerBoundedEval, hp]
  | exSubset i p hp =>
    simp only [PowerBoundedFormula.toFormula, Eval, eval_powerSubsetFormula, cons_zero, cons_succ,
      PowerBoundedEval, hp]
  | allSubset i p hp =>
    simp only [PowerBoundedFormula.toFormula, Eval, eval_powerSubsetFormula, cons_zero, cons_succ,
      PowerBoundedEval, hp]

def PowerBoundedFormula.depth : {n : Nat} → PowerBoundedFormula n → Nat
  | _, .equal _ _ | _, .member _ _ | _, .bottom => 0
  | _, .conj p q | _, .impl p q => max p.depth q.depth
  | _, .exMem _ p | _, .allMem _ p | _, .exSubset _ p | _, .allSubset _ p => p.depth + 1

def PowerBoundedSeparation (s : U → U → Prop) : Prop :=
  ∀ n (p : PowerBoundedFormula (n+1)) (v : Fin n → U) (a : U),
    ∃ b, ∀ x, s x b ↔ s x a ∧ PowerBoundedEval s p (cons x v)

/-- A semantic assertion about a finite external quantifier depth, not an
    internal omega sequence or a transitive-closure assumption. -/
def PowerQuantifierControl (s : U → U → Prop) (B : U) : Nat → U → Prop
  | 0, _ => True
  | n+1, x => ∀ y, (s y x ∨ Subset s y x) → s y B ∧ PowerQuantifierControl s B n y

#print axioms power_bounded_eval_toFormula
end FullBridge
