import ScheduledSchemeCriteria
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def prefixEnv {k : Nat} (v : Fin k → U) : {n : Nat} → (Fin n → U) → Fin (k+n) → U
  | 0, _ => v
  | n+1, xs => cons (xs 0) (prefixEnv v (fun i : Fin n => xs i.succ))

def prefixRename {k l : Nat} (f : Fin k → Fin l) : (n : Nat) → Fin (k+n) → Fin (l+n)
  | 0 => f
  | n+1 => liftRename (prefixRename f n)

def prefixIndex {k : Nat} (i : Fin k) : (n : Nat) → Fin (k+n)
  | 0 => i
  | n+1 => (prefixIndex i n).succ

theorem prefix_env_index {k n} (v : Fin k → U) (xs : Fin n → U) (i : Fin k) :
    prefixEnv v xs (prefixIndex i n) = v i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (fun j => xs j.succ)

theorem prefix_env_rename {k l n} (f : Fin k → Fin l) (v : Fin l → U) (xs : Fin n → U) :
    (fun i => prefixEnv v xs (prefixRename f n i)) = prefixEnv (fun i => v (f i)) xs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (fun i => cons (xs 0) (prefixEnv v (fun j => xs j.succ))
      (liftRename (prefixRename f n) i)) = _
    rw [cons_lift, ih]
    rfl

def allPrefix {k : Nat} (a : Fin k) : (n : Nat) → Formula (k+n) → Formula k
  | 0, p => p
  | n+1, p => allPrefix a n (.all (.impl (.member 0 (prefixIndex a n).succ) p))

theorem eval_allPrefix {k n} (a : Fin k) (p : Formula (k+n)) (v : Fin k → U) :
    Eval s (allPrefix a n p) v ↔
      ∀ xs : Fin n → U, (∀ i, s (xs i) (v a)) → Eval s p (prefixEnv v xs) := by
  induction n with
  | zero =>
    constructor
    · exact fun h _ _ => h
    · intro h
      exact h Fin.elim0 (fun i => Fin.elim0 i)
  | succ n ih =>
    rw [allPrefix, ih]
    constructor
    · intro h xs hx
      have hh := h (fun i => xs i.succ) (fun i => hx i.succ)
      change ∀ x, s x (prefixEnv v (fun i => xs i.succ) (prefixIndex a n)) → _ at hh
      rw [prefix_env_index] at hh
      exact hh (xs 0) (hx 0)
    · intro h xs hx
      change ∀ x, s x (prefixEnv v xs (prefixIndex a n)) → _
      rw [prefix_env_index]
      intro x hxa
      exact h (cons x xs) (fun i => Fin.cases hxa hx i)

def prefixWitnessBoundFormula {k : Nat} (n : Nat) (p : Formula (k+n+1)) : Formula (k+2) :=
  allPrefix 1 n (.ex (.conj (.member 0 (prefixIndex (0 : Fin (k+2)) n).succ)
    (p.rename (liftRename (prefixRename (fun i : Fin k => i.succ.succ) n)))))

theorem eval_prefixWitnessBoundFormula {k n} (p : Formula (k+n+1)) (b a : U) (v : Fin k → U) :
    Eval s (prefixWitnessBoundFormula n p) (cons b (cons a v)) ↔
      ∀ xs : Fin n → U, (∀ i, s (xs i) a) →
        ∃ y, s y b ∧ Eval s p (cons y (prefixEnv v xs)) := by
  rw [prefixWitnessBoundFormula, eval_allPrefix]
  apply forall_congr'
  intro xs
  apply imp_congr Iff.rfl
  simp only [Eval, cons_zero, cons_succ, prefix_env_index, eval_rename, cons_lift, prefix_env_rename]

def insertAfterPrefix {k : Nat} (n : Nat) : Fin (k+n+1) → Fin (k+1+n) :=
  Fin.cases (prefixIndex 0 n) (prefixRename Fin.succ n)

theorem insert_after_prefix_env {k n} (x : U) (v : Fin k → U) (xs : Fin n → U) :
    (fun i => prefixEnv (cons x v) xs (insertAfterPrefix n i)) = cons x (prefixEnv v xs) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact prefix_env_index (cons x v) xs 0
  · exact congrFun (prefix_env_rename Fin.succ (cons x v) xs) j

def switchSecondThird {k : Nat} : Fin (k+3) → Fin (k+3) :=
  Fin.cases 0 (Fin.cases 2 (Fin.cases 1 (fun i => i.succ.succ.succ)))

theorem switch_second_third_env {k} (b x a : U) (v : Fin k → U) :
    (fun i => cons b (cons x (cons a v)) (switchSecondThird i)) = cons b (cons a (cons x v)) := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun _ => rfl) i) i) i

/-- Iterated Collection bounds all finite input tuples in a, using actual
    formulas and source unions, without external predicate comprehension. -/
theorem finite_context_collection (hc : Collection s) (hp : Pairing s) (hu : Union s)
    {k} (n : Nat) (p : Formula (k+n+1)) (v : Fin k → U) (a : U)
    (ht : ∀ xs : Fin n → U, (∀ i, s (xs i) a) → ∃ y, Eval s p (cons y (prefixEnv v xs))) :
    ∃ b, ∀ xs : Fin n → U, (∀ i, s (xs i) a) →
      ∃ y, s y b ∧ Eval s p (cons y (prefixEnv v xs)) := by
  induction n generalizing k with
  | zero =>
    obtain ⟨y, hy⟩ := ht Fin.elim0 (fun i => Fin.elim0 i)
    obtain ⟨b, hb⟩ := hp y y
    exact ⟨b, fun _ _ => ⟨y, (hb y).mpr (Or.inl rfl), hy⟩⟩
  | succ n ih =>
    let q : Formula (k+1+n+1) := p.rename (liftRename (insertAfterPrefix n))
    have hq : ∀ x xs y, Eval s q (cons y (prefixEnv (cons x v) xs)) ↔
        Eval s p (cons y (prefixEnv v (cons x xs))) := by
      intro x xs y
      dsimp only [q]
      rw [eval_rename, cons_lift, insert_after_prefix_env]
      rfl
    let r : Formula (k+3) := (prefixWitnessBoundFormula n q).rename switchSecondThird
    have hr : ∀ b x, Eval s r (cons b (cons x (cons a v))) ↔
        ∀ xs : Fin n → U, (∀ i, s (xs i) a) →
          ∃ y, s y b ∧ Eval s p (cons y (prefixEnv v (cons x xs))) := by
      intro b x
      dsimp only [r]
      rw [eval_rename, switch_second_third_env, eval_prefixWitnessBoundFormula]
      apply forall_congr'
      intro xs
      apply imp_congr Iff.rfl
      exact exists_congr (fun y => and_congr Iff.rfl (hq x xs y))
    obtain ⟨B, hB⟩ := hc (k+1) r (cons a v) a (by
      intro x hx
      obtain ⟨b, hb⟩ := ih q (cons x v) (by
        intro xs hxs
        obtain ⟨y, hy⟩ := ht (cons x xs) (fun i => Fin.cases hx hxs i)
        exact ⟨y, (hq x xs y).mpr hy⟩)
      refine ⟨b, (hr b x).mpr ?_⟩
      intro xs hxs
      obtain ⟨y, hyb, hy⟩ := hb xs hxs
      exact ⟨y, hyb, (hq x xs y).mp hy⟩)
    obtain ⟨b, hb⟩ := hu B
    refine ⟨b, fun xs hxs => ?_⟩
    obtain ⟨c, hcB, hcx⟩ := hB (xs 0) (hxs 0)
    obtain ⟨y, hyc, hy⟩ := (hr c (xs 0)).mp hcx (fun i => xs i.succ) (fun i => hxs i.succ)
    have he : cons (xs 0) (fun i => xs i.succ) = xs := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [he] at hy
    exact ⟨y, (hb y).mpr ⟨c, hcB, hyc⟩, hy⟩

theorem prefix_env_nil {n} (xs : Fin n → U) :
    prefixEnv (k := 0) Fin.elim0 xs = fun i => xs (Fin.cast (Nat.zero_add n) i) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (fun j => xs j.succ)) j

/-- A single source witness bound for every input tuple where a witness
    exists. The relation may be arbitrary first-order, not bounded. -/
theorem finite_context_partial_collection (hc : Collection s) (hp : Pairing s) (hu : Union s)
    {n} (p : Formula (n+1)) (a : U) :
    ∃ b, ∀ xs : Fin n → U, (∀ i, s (xs i) a) →
      (∃ y, Eval s p (cons y xs)) → ∃ y, s y b ∧ Eval s p (cons y xs) := by
  classical
  let q : Formula (n+1) := .impl ((Formula.ex p).rename Fin.succ) p
  have hq : ∀ y xs, Eval s q (cons y xs) ↔
      ((∃ z, Eval s p (cons z xs)) → Eval s p (cons y xs)) := by
    intro y xs
    simp only [q, Eval, eval_rename, cons_succ]
  let r : Formula (0+n+1) := q.rename (liftRename (Fin.cast (Nat.zero_add n).symm))
  have hr : ∀ y xs, Eval s r (cons y (prefixEnv Fin.elim0 xs)) ↔ Eval s q (cons y xs) := by
    intro y xs
    dsimp only [r]
    rw [eval_rename, cons_lift]
    have he : (fun i => prefixEnv (k := 0) Fin.elim0 xs (Fin.cast (Nat.zero_add n).symm i)) = xs := by
      rw [prefix_env_nil]
      rfl
    rw [he]
  obtain ⟨b, hb⟩ := finite_context_collection hc hp hu n r Fin.elim0 a (by
    intro xs _
    by_cases h : ∃ y, Eval s p (cons y xs)
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, (hr y xs).mpr ((hq y xs).mpr (fun _ => hy))⟩
    · exact ⟨a, (hr a xs).mpr ((hq a xs).mpr (fun he => False.elim (h he)))⟩)
  refine ⟨b, fun xs hx hex => ?_⟩
  obtain ⟨y, hyb, hy⟩ := hb xs hx
  exact ⟨y, hyb, (hq y xs).mp ((hr y xs).mp hy) hex⟩

#print axioms finite_context_partial_collection
end FullBridge
