import FiniteContextCollection
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def BoundedFormula.rename : {n m : Nat} → (Fin n → Fin m) → BoundedFormula n → BoundedFormula m
  | _, _, f, .equal i j => .equal (f i) (f j)
  | _, _, f, .member i j => .member (f i) (f j)
  | _, _, _, .bottom => .bottom
  | _, _, f, .conj p q => .conj (p.rename f) (q.rename f)
  | _, _, f, .impl p q => .impl (p.rename f) (q.rename f)
  | _, _, f, .exMem i p => .exMem (f i) (p.rename (liftRename f))
  | _, _, f, .allMem i p => .allMem (f i) (p.rename (liftRename f))

theorem bounded_eval_rename {n m} (p : BoundedFormula n) (f : Fin n → Fin m) (v : Fin m → U) :
    BoundedEval s (p.rename f) v ↔ BoundedEval s p (fun i => v (f i)) := by
  induction p generalizing m with
  | equal => rfl
  | member => rfl
  | bottom => rfl
  | conj p q hp hq => simp only [BoundedFormula.rename, BoundedEval, hp, hq]
  | impl p q hp hq => simp only [BoundedFormula.rename, BoundedEval, hp, hq]
  | exMem i p hp => simp only [BoundedFormula.rename, BoundedEval, hp, cons_lift]
  | allMem i p hp => simp only [BoundedFormula.rename, BoundedEval, hp, cons_lift]

def joinEnv {k l} (v : Fin k → U) (w : Fin l → U) : Fin (k+l) → U := Fin.addCases v w

theorem join_env_left {k l} (v : Fin k → U) (w : Fin l → U) :
    (fun i => joinEnv v w (Fin.castAdd l i)) = v := by
  funext i
  simp [joinEnv]

theorem join_env_right {k l} (v : Fin k → U) (w : Fin l → U) :
    (fun i => joinEnv v w (Fin.natAdd k i)) = w := by
  funext i
  simp [joinEnv]

/-- A bounded definition on a fixed input set, with finitely many actual
    source parameters. The definition may depend on this input set. -/
def LocallyBoundedFormula (s : U → U → Prop) {n} (p : Formula n) (a : U) : Prop :=
  ∃ k, ∃ q : BoundedFormula (k+n), ∃ v : Fin k → U, ∀ xs : Fin n → U,
    (∀ i, s (xs i) a) → (BoundedEval s q (prefixEnv v xs) ↔ Eval s p xs)

theorem collection_local_bounded_definitions (hc : Collection s) (hp : Pairing s) (hu : Union s)
    {n} (p : Formula n) (a : U) : LocallyBoundedFormula s p a := by
  classical
  induction p generalizing a with
  | equal i j =>
    refine ⟨0, .equal (Fin.cast (Nat.zero_add _).symm i) (Fin.cast (Nat.zero_add _).symm j),
      Fin.elim0, fun xs _ => ?_⟩
    simp only [BoundedEval, Eval, prefix_env_nil]
    rfl
  | member i j =>
    refine ⟨0, .member (Fin.cast (Nat.zero_add _).symm i) (Fin.cast (Nat.zero_add _).symm j),
      Fin.elim0, fun xs _ => ?_⟩
    simp only [BoundedEval, Eval, prefix_env_nil]
    rfl
  | bottom => exact ⟨0, .bottom, Fin.elim0, fun _ _ => Iff.rfl⟩
  | @conj n p r ihp ihr =>
    obtain ⟨k, q, v, hq⟩ := ihp a
    obtain ⟨l, t, w, ht⟩ := ihr a
    refine ⟨k+l, .conj (q.rename (prefixRename (Fin.castAdd l) n))
      (t.rename (prefixRename (Fin.natAdd k) n)), joinEnv v w, fun xs hxs => ?_⟩
    simp only [BoundedEval, bounded_eval_rename, prefix_env_rename, join_env_left, join_env_right]
    exact and_congr (hq xs hxs) (ht xs hxs)
  | @impl n p r ihp ihr =>
    obtain ⟨k, q, v, hq⟩ := ihp a
    obtain ⟨l, t, w, ht⟩ := ihr a
    refine ⟨k+l, .impl (q.rename (prefixRename (Fin.castAdd l) n))
      (t.rename (prefixRename (Fin.natAdd k) n)), joinEnv v w, fun xs hxs => ?_⟩
    simp only [BoundedEval, bounded_eval_rename, prefix_env_rename, join_env_left, join_env_right]
    exact imp_congr (hq xs hxs) (ht xs hxs)
  | @ex n p ih =>
    obtain ⟨b, hb⟩ := finite_context_partial_collection hc hp hu p a
    obtain ⟨d, hd⟩ := binary_union_exists hp hu a b
    obtain ⟨k, q, v, hq⟩ := ih d
    refine ⟨k+1, .exMem (prefixIndex 0 n) (q.rename (prefixRename Fin.succ (n+1))),
      cons b v, fun xs hxs => ?_⟩
    have he : ∀ y, (fun i => cons y (prefixEnv (cons b v) xs)
        (prefixRename Fin.succ (n+1) i)) = prefixEnv v (cons y xs) := by
      intro y
      change (fun i => cons y (prefixEnv (cons b v) xs)
        (liftRename (prefixRename Fin.succ n) i)) = _
      rw [cons_lift, prefix_env_rename]
      rfl
    simp only [BoundedEval, prefix_env_index, cons_zero, bounded_eval_rename, he]
    change (∃ y, s y b ∧ BoundedEval s q (prefixEnv v (cons y xs))) ↔ ∃ y, Eval s p (cons y xs)
    constructor
    · rintro ⟨y, hyb, hy⟩
      exact ⟨y, (hq (cons y xs) (fun i => Fin.cases ((hd y).mpr (Or.inr hyb))
        (fun j => (hd _).mpr (Or.inl (hxs j))) i)).mp hy⟩
    · intro he
      obtain ⟨y, hyb, hy⟩ := hb xs hxs he
      exact ⟨y, hyb, (hq (cons y xs) (fun i => Fin.cases ((hd y).mpr (Or.inr hyb))
        (fun j => (hd _).mpr (Or.inl (hxs j))) i)).mpr hy⟩
  | @all n p ih =>
    obtain ⟨b, hb⟩ := finite_context_partial_collection hc hp hu (Formula.impl p .bottom) a
    obtain ⟨d, hd⟩ := binary_union_exists hp hu a b
    obtain ⟨k, q, v, hq⟩ := ih d
    refine ⟨k+1, .allMem (prefixIndex 0 n) (q.rename (prefixRename Fin.succ (n+1))),
      cons b v, fun xs hxs => ?_⟩
    have he : ∀ y, (fun i => cons y (prefixEnv (cons b v) xs)
        (prefixRename Fin.succ (n+1) i)) = prefixEnv v (cons y xs) := by
      intro y
      change (fun i => cons y (prefixEnv (cons b v) xs)
        (liftRename (prefixRename Fin.succ n) i)) = _
      rw [cons_lift, prefix_env_rename]
      rfl
    simp only [BoundedEval, prefix_env_index, cons_zero, bounded_eval_rename, he]
    change (∀ y, s y b → BoundedEval s q (prefixEnv v (cons y xs))) ↔ ∀ y, Eval s p (cons y xs)
    constructor
    · intro h y
      apply Classical.byContradiction
      intro hy
      obtain ⟨z, hzb, hz⟩ := hb xs hxs ⟨y, hy⟩
      exact hz ((hq (cons z xs) (fun i => Fin.cases ((hd z).mpr (Or.inr hzb))
        (fun j => (hd _).mpr (Or.inl (hxs j))) i)).mp (h z hzb))
    · intro h y hyb
      exact (hq (cons y xs) (fun i => Fin.cases ((hd y).mpr (Or.inr hyb))
        (fun j => (hd _).mpr (Or.inl (hxs j))) i)).mpr (h y)

#print axioms collection_local_bounded_definitions
end FullBridge
