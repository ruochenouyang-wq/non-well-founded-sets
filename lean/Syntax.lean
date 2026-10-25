import Std

/- First-order equality and membership, with a finite context of free variables.
   A bound variable is inserted at index zero.  No model axioms are assumed. -/
namespace FullBridge
universe u

inductive Formula : Nat → Type where
  | equal {n} : Fin n → Fin n → Formula n
  | member {n} : Fin n → Fin n → Formula n
  | bottom {n} : Formula n
  | conj {n} : Formula n → Formula n → Formula n
  | impl {n} : Formula n → Formula n → Formula n
  | ex {n} : Formula (n + 1) → Formula n
  | all {n} : Formula (n + 1) → Formula n

def cons {U : Type u} {n : Nat} (x : U) (v : Fin n → U) : Fin (n + 1) → U :=
  Fin.cases x v

@[simp] theorem cons_zero {U : Type u} {n} (x : U) (v : Fin n → U) :
    cons x v 0 = x := rfl
@[simp] theorem cons_succ {U : Type u} {n} (x : U) (v : Fin n → U) (i : Fin n) :
    cons x v i.succ = v i := rfl

def Eval {U : Type u} (mem : U → U → Prop) :
    {n : Nat} → Formula n → (Fin n → U) → Prop
  | _, .equal i j, v => v i = v j
  | _, .member i j, v => mem (v i) (v j)
  | _, .bottom, _ => False
  | _, .conj p q, v => Eval mem p v ∧ Eval mem q v
  | _, .impl p q, v => Eval mem p v → Eval mem q v
  | _, .ex p, v => ∃ x, Eval mem p (cons x v)
  | _, .all p, v => ∀ x, Eval mem p (cons x v)

def liftRename {n m : Nat} (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

def Formula.rename : {n m : Nat} → (Fin n → Fin m) → Formula n → Formula m
  | _, _, f, .equal i j => .equal (f i) (f j)
  | _, _, f, .member i j => .member (f i) (f j)
  | _, _, _, .bottom => .bottom
  | _, _, f, .conj p q => .conj (p.rename f) (q.rename f)
  | _, _, f, .impl p q => .impl (p.rename f) (q.rename f)
  | _, _, f, .ex p => .ex (p.rename (liftRename f))
  | _, _, f, .all p => .all (p.rename (liftRename f))

theorem cons_lift {U : Type u} {n m} (f : Fin n → Fin m) (x : U) (v : Fin m → U) :
    (fun i => cons x v (liftRename f i)) = cons x (fun i => v (f i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem eval_rename {U : Type u} (mem : U → U → Prop) {n m}
    (p : Formula n) (f : Fin n → Fin m) (v : Fin m → U) :
    Eval mem (p.rename f) v ↔ Eval mem p (fun i => v (f i)) := by
  induction p generalizing m with
  | equal => rfl
  | member => rfl
  | bottom => rfl
  | conj p q hp hq => simp only [Formula.rename, Eval, hp, hq]
  | impl p q hp hq => simp only [Formula.rename, Eval, hp, hq]
  | ex p hp => simp only [Formula.rename, Eval, hp, cons_lift]
  | all p hp => simp only [Formula.rename, Eval, hp, cons_lift]

/- Image predicate with free variables [y, a, parameters] and bound x.
   The relation p has free variables [y, x, parameters]. -/
def imageRename {n : Nat} : Fin (n + 2) → Fin (n + 3) :=
  Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ.succ))

def imageFormula {n : Nat} (p : Formula (n + 2)) : Formula (n + 2) :=
  .ex (.conj (.member 0 2) (p.rename imageRename))

theorem image_env {U : Type u} {n} (x y a : U) (v : Fin n → U) :
    (fun i => cons x (cons y (cons a v)) (imageRename i)) = cons y (cons x v) := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i

theorem eval_image {U : Type u} (mem : U → U → Prop) {n}
    (p : Formula (n + 2)) (y a : U) (v : Fin n → U) :
    Eval mem (imageFormula p) (cons y (cons a v)) ↔
      ∃ x, mem x a ∧ Eval mem p (cons y (cons x v)) := by
  simp only [imageFormula, Eval, eval_rename, image_env]
  rfl

end FullBridge
