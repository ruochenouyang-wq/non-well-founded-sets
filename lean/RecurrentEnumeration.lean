import ActionEmbeddingSemantics
namespace FullBridge
universe u

def diagonalState : Nat → Nat × Nat
  | 0 => (0, 0)
  | n+1 => let p := diagonalState n
      if p.2 < p.1 then (p.1, p.2+1) else (p.1+1, 0)

def diagonalStart : Nat → Nat
  | 0 => 0
  | n+1 => diagonalStart n + n + 1

theorem diagonal_block (start n : Nat) (h : diagonalState start = (n, 0)) :
    ∀ j, j ≤ n → diagonalState (start+j) = (n,j) := by
  intro j
  induction j with
  | zero => intro _; simpa using h
  | succ j ih =>
    intro hj
    have hjn : j < n := by omega
    have hjle : j ≤ n := by omega
    have he : start+(j+1) = (start+j)+1 := by omega
    rw [he, diagonalState, ih hjle]
    simp only [hjn, ↓reduceIte]

theorem diagonal_start_value (n : Nat) : diagonalState (diagonalStart n) = (n,0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hend := diagonal_block (diagonalStart n) n ih n (Nat.le_refl n)
    rw [diagonalStart, diagonalState, hend]
    simp

theorem diagonal_start_ge (n : Nat) : n ≤ diagonalStart n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => simp only [diagonalStart]; omega

/-- Each external index recurs after every external stage. -/
theorem diagonal_index_cofinal (k lower : Nat) :
    ∃ n, lower ≤ n ∧ (diagonalState n).2 = k := by
  let b := k+lower
  refine ⟨diagonalStart b+k, ?_, ?_⟩
  · have hb := diagonal_start_ge b
    dsimp [b] at *
    omega
  · rw [diagonal_block (diagonalStart b) b (diagonal_start_value b) k (by dsimp [b]; omega)]

def recurrentEnum {U : Type u} (enum : Nat → U) (n : Nat) : U := enum (diagonalState n).2

theorem recurrent_enum_cofinal {U : Type u} (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x)
    (x : U) (lower : Nat) : ∃ n, lower ≤ n ∧ recurrentEnum enum n = x := by
  obtain ⟨k, hk⟩ := henum x
  obtain ⟨n, hn, hnk⟩ := diagonal_index_cofinal k lower
  exact ⟨n, hn, by simp only [recurrentEnum, hnk, hk]⟩

theorem recurrent_enum_onto {U : Type u} (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∀ x, ∃ n, recurrentEnum enum n = x := by
  intro x
  obtain ⟨n, _, hn⟩ := recurrent_enum_cofinal enum henum x 0
  exact ⟨n, hn⟩

#print axioms recurrent_enum_cofinal
end FullBridge
