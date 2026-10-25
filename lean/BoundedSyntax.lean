import SupportedInfinity
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Bounded quantifiers range over a variable from the current environment;
    the bound variable itself is inserted at position zero in the body. -/
inductive BoundedFormula : Nat → Type where
  | equal {n} : Fin n → Fin n → BoundedFormula n
  | member {n} : Fin n → Fin n → BoundedFormula n
  | bottom {n} : BoundedFormula n
  | conj {n} : BoundedFormula n → BoundedFormula n → BoundedFormula n
  | impl {n} : BoundedFormula n → BoundedFormula n → BoundedFormula n
  | exMem {n} : Fin n → BoundedFormula (n+1) → BoundedFormula n
  | allMem {n} : Fin n → BoundedFormula (n+1) → BoundedFormula n

def BoundedFormula.toFormula : {n : Nat} → BoundedFormula n → Formula n
  | _, .equal i j => .equal i j
  | _, .member i j => .member i j
  | _, .bottom => .bottom
  | _, .conj p q => .conj p.toFormula q.toFormula
  | _, .impl p q => .impl p.toFormula q.toFormula
  | _, .exMem i p => .ex (.conj (.member 0 i.succ) p.toFormula)
  | _, .allMem i p => .all (.impl (.member 0 i.succ) p.toFormula)

def BoundedEval (s : U → U → Prop) : {n : Nat} → BoundedFormula n → (Fin n → U) → Prop
  | _, .equal i j, v => v i = v j
  | _, .member i j, v => s (v i) (v j)
  | _, .bottom, _ => False
  | _, .conj p q, v => BoundedEval s p v ∧ BoundedEval s q v
  | _, .impl p q, v => BoundedEval s p v → BoundedEval s q v
  | _, .exMem i p, v => ∃ x, s x (v i) ∧ BoundedEval s p (cons x v)
  | _, .allMem i p, v => ∀ x, s x (v i) → BoundedEval s p (cons x v)

theorem bounded_eval_toFormula {n} (p : BoundedFormula n) (v : Fin n → U) :
    Eval s p.toFormula v ↔ BoundedEval s p v := by
  induction p with
  | equal => rfl
  | member => rfl
  | bottom => rfl
  | conj p q hp hq => exact and_congr (hp v) (hq v)
  | impl p q hp hq => exact imp_congr (hp v) (hq v)
  | exMem i p hp =>
    simp only [BoundedFormula.toFormula, Eval, cons_zero, cons_succ, BoundedEval, hp]
  | allMem i p hp =>
    simp only [BoundedFormula.toFormula, Eval, cons_zero, cons_succ, BoundedEval, hp]

theorem supported_cons_values {swap : Nat → U → U} {n}
    (x : SupportedCarrier s swap) (v : Fin n → SupportedCarrier s swap) :
    (fun i => (cons x v i).val) = cons x.val (fun i => (v i).val) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem supported_bounded_absoluteness {swap : Nat → U → U} {n} (p : BoundedFormula n)
    (v : Fin n → SupportedCarrier s swap) :
    BoundedEval (supportedMember swap) p v ↔ BoundedEval s p (fun i => (v i).val) := by
  induction p with
  | equal i j => exact ⟨congrArg Subtype.val, Subtype.ext⟩
  | member => rfl
  | bottom => rfl
  | conj p q hp hq => exact and_congr (hp v) (hq v)
  | impl p q hp hq => exact imp_congr (hp v) (hq v)
  | exMem i p hp =>
    constructor
    · rintro ⟨x, hx, hpx⟩
      exact ⟨x.val, hx, by simpa only [supported_cons_values] using (hp (cons x v)).mp hpx⟩
    · rintro ⟨x, hx, hpx⟩
      let X : SupportedCarrier s swap := ⟨x, hereditary_support_member (v i).property hx⟩
      exact ⟨X, hx, (hp (cons X v)).mpr (by simpa only [supported_cons_values] using hpx)⟩
  | allMem i p hp =>
    constructor
    · intro h x hx
      let X : SupportedCarrier s swap := ⟨x, hereditary_support_member (v i).property hx⟩
      simpa only [supported_cons_values] using (hp (cons X v)).mp (h X hx)
    · intro h x hx
      exact (hp (cons x v)).mpr (by simpa only [supported_cons_values] using h x.val hx)

def BoundedSeparation (s : U → U → Prop) : Prop :=
  ∀ n (p : BoundedFormula (n+1)) (v : Fin n → U) (a : U),
    ∃ b, ∀ x, s x b ↔ s x a ∧ BoundedEval s p (cons x v)

#print axioms supported_bounded_absoluteness
end FullBridge
