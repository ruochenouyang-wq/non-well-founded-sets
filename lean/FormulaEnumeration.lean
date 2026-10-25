import RecurrentEnumeration

/- External natural-number enumerations of the actual finite formula syntax
   and of finite tuples.  These are metatheoretic enumerations, not assertions
   about a model's internal natural numbers. -/
namespace FullBridge

def natPairCode (a b : Nat) : Nat := diagonalStart (a + b) + b

def natPairDecode (k : Nat) : Nat × Nat :=
  ((diagonalState k).1 - (diagonalState k).2, (diagonalState k).2)

@[simp] theorem natPairDecode_code (a b : Nat) :
    natPairDecode (natPairCode a b) = (a, b) := by
  unfold natPairDecode natPairCode
  rw [diagonal_block (diagonalStart (a+b)) (a+b) (diagonal_start_value (a+b)) b (by omega)]
  simp

def natTupleEnumeration : (n : Nat) → Nat → (Fin n → Nat)
  | 0, _ => Fin.elim0
  | n+1, k => cons (natPairDecode k).1 (natTupleEnumeration n (natPairDecode k).2)

def natTupleCode : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | _+1, v => natPairCode (v 0) (natTupleCode (fun i => v i.succ))

@[simp] theorem natTupleEnumeration_code {n : Nat} (v : Fin n → Nat) :
    natTupleEnumeration n (natTupleCode v) = v := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [natTupleCode, natTupleEnumeration, natPairDecode_code, ih]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem natTupleEnumeration_onto (n : Nat) (v : Fin n → Nat) :
    ∃ k, natTupleEnumeration n k = v := ⟨natTupleCode v, natTupleEnumeration_code v⟩

def Formula.natCode : {n : Nat} → Formula n → Nat
  | _, .equal i j => natPairCode 0 (natPairCode i.val j.val)
  | _, .member i j => natPairCode 1 (natPairCode i.val j.val)
  | _, .bottom => natPairCode 2 0
  | _, .conj p q => natPairCode 3 (natPairCode p.natCode q.natCode)
  | _, .impl p q => natPairCode 4 (natPairCode p.natCode q.natCode)
  | _, .ex p => natPairCode 5 p.natCode
  | _, .all p => natPairCode 6 p.natCode

def Formula.decodeFuel : {n : Nat} → Formula n → Nat
  | _, .equal _ _ => 1
  | _, .member _ _ => 1
  | _, .bottom => 1
  | _, .conj p q => p.decodeFuel + q.decodeFuel + 1
  | _, .impl p q => p.decodeFuel + q.decodeFuel + 1
  | _, .ex p => p.decodeFuel + 1
  | _, .all p => p.decodeFuel + 1

def formulaDecode : Nat → (n : Nat) → Nat → Formula n
  | 0, _, _ => .bottom
  | fuel+1, n, k =>
    let payload := (natPairDecode k).2
    let pair := natPairDecode payload
    match (natPairDecode k).1 with
    | 0 => if hi : pair.1 < n then
        if hj : pair.2 < n then .equal ⟨pair.1, hi⟩ ⟨pair.2, hj⟩ else .bottom
        else .bottom
    | 1 => if hi : pair.1 < n then
        if hj : pair.2 < n then .member ⟨pair.1, hi⟩ ⟨pair.2, hj⟩ else .bottom
        else .bottom
    | 2 => .bottom
    | 3 => .conj (formulaDecode fuel n pair.1) (formulaDecode fuel n pair.2)
    | 4 => .impl (formulaDecode fuel n pair.1) (formulaDecode fuel n pair.2)
    | 5 => .ex (formulaDecode fuel (n+1) payload)
    | 6 => .all (formulaDecode fuel (n+1) payload)
    | _ => .bottom

theorem formulaDecode_code {n : Nat} (p : Formula n) (fuel : Nat)
    (h : p.decodeFuel ≤ fuel) : formulaDecode fuel n p.natCode = p := by
  induction p generalizing fuel with
  | equal i j =>
    cases fuel with
    | zero => simp [Formula.decodeFuel] at h
    | succ fuel => simp [formulaDecode, Formula.natCode, i.isLt, j.isLt]
  | member i j =>
    cases fuel with
    | zero => simp [Formula.decodeFuel] at h
    | succ fuel => simp [formulaDecode, Formula.natCode, i.isLt, j.isLt]
  | bottom =>
    cases fuel with
    | zero => simp [Formula.decodeFuel] at h
    | succ fuel => simp [formulaDecode, Formula.natCode]
  | conj p q hp hq =>
    cases fuel with
    | zero => simp [Formula.decodeFuel] at h
    | succ fuel =>
      simp only [Formula.decodeFuel] at h
      simp only [Formula.natCode, formulaDecode, natPairDecode_code]
      rw [hp fuel (by omega), hq fuel (by omega)]
  | impl p q hp hq =>
    cases fuel with
    | zero => simp [Formula.decodeFuel] at h
    | succ fuel =>
      simp only [Formula.decodeFuel] at h
      simp only [Formula.natCode, formulaDecode, natPairDecode_code]
      rw [hp fuel (by omega), hq fuel (by omega)]
  | ex p hp =>
    cases fuel with
    | zero => simp [Formula.decodeFuel] at h
    | succ fuel =>
      simp only [Formula.decodeFuel] at h
      simp only [Formula.natCode, formulaDecode, natPairDecode_code]
      exact congrArg Formula.ex (hp fuel (by omega))
  | all p hp =>
    cases fuel with
    | zero => simp [Formula.decodeFuel] at h
    | succ fuel =>
      simp only [Formula.decodeFuel] at h
      simp only [Formula.natCode, formulaDecode, natPairDecode_code]
      exact congrArg Formula.all (hp fuel (by omega))

def formulaEnumeration (n k : Nat) : Formula n :=
  formulaDecode (natPairDecode k).1 n (natPairDecode k).2

theorem formulaEnumeration_onto (n : Nat) (p : Formula n) :
    ∃ k, formulaEnumeration n k = p := by
  refine ⟨natPairCode p.decodeFuel p.natCode, ?_⟩
  simp only [formulaEnumeration, natPairDecode_code]
  exact formulaDecode_code p _ (Nat.le_refl _)

end FullBridge
