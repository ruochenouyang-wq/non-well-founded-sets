import PowerQuantifierBounds
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def boundedSubsetFormula {n} (i j : Fin n) : BoundedFormula n :=
  .allMem i (.member 0 j.succ)

theorem bounded_eval_subset {n} (i j : Fin n) (v : Fin n → U) :
    BoundedEval s (boundedSubsetFormula i j) v ↔ Subset s (v i) (v j) := by rfl

def powerBoundLift {n m} (r : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (fun i => (r i).succ)

theorem power_bound_lift_env {n m} (r : Fin n → Fin m) (v : Fin m → U) (x : U) :
    (fun i => cons x v (powerBoundLift r i)) = cons x (fun i => v (r i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

def PowerBoundedFormula.restrict : {n : Nat} → PowerBoundedFormula n →
    {m : Nat} → (Fin n → Fin m) → Fin m → BoundedFormula m
  | _, .equal i j, _, r, _ => .equal (r i) (r j)
  | _, .member i j, _, r, _ => .member (r i) (r j)
  | _, .bottom, _, _, _ => .bottom
  | _, .conj p q, _, r, b => .conj (p.restrict r b) (q.restrict r b)
  | _, .impl p q, _, r, b => .impl (p.restrict r b) (q.restrict r b)
  | _, .exMem i p, _, r, b => .exMem (r i) (p.restrict (powerBoundLift r) b.succ)
  | _, .allMem i p, _, r, b => .allMem (r i) (p.restrict (powerBoundLift r) b.succ)
  | _, .exSubset i p, _, r, b => .exMem b
      (.conj (boundedSubsetFormula 0 (r i).succ) (p.restrict (powerBoundLift r) b.succ))
  | _, .allSubset i p, _, r, b => .allMem b
      (.impl (boundedSubsetFormula 0 (r i).succ) (p.restrict (powerBoundLift r) b.succ))

theorem power_control_cons {n k} {B x : U} {v : Fin n → U}
    (h : ∀ i, PowerQuantifierControl s B (k+1) (v i)) (i : Fin n)
    (hx : s x (v i) ∨ Subset s x (v i)) :
    ∀ j, PowerQuantifierControl s B k (cons x v j) := by
  intro j
  exact Fin.cases (h i x hx).2
    (fun l => power_control_depth_mono (Nat.le_succ k) (h l)) j

/-- The bound is constructed later from the finite syntax depth. No assertion
    that arbitrary unbounded truth is internally definable is used here. -/
theorem power_bounded_restrict_correct {n} (p : PowerBoundedFormula n) {m}
    (r : Fin n → Fin m) (b : Fin m) (v : Fin m → U)
    (h : ∀ i, PowerQuantifierControl s (v b) p.depth (v (r i))) :
    BoundedEval s (p.restrict r b) v ↔ PowerBoundedEval s p (fun i => v (r i)) := by
  induction p generalizing m with
  | equal => rfl
  | member => rfl
  | bottom => rfl
  | conj p q hp hq =>
    exact and_congr
      (hp r b v (fun i => power_control_depth_mono (Nat.le_max_left _ _) (h i)))
      (hq r b v (fun i => power_control_depth_mono (Nat.le_max_right _ _) (h i)))
  | impl p q hp hq =>
    exact imp_congr
      (hp r b v (fun i => power_control_depth_mono (Nat.le_max_left _ _) (h i)))
      (hq r b v (fun i => power_control_depth_mono (Nat.le_max_right _ _) (h i)))
  | exMem i p hp =>
    have step : ∀ x, s x (v (r i)) →
        (BoundedEval s (p.restrict (powerBoundLift r) b.succ) (cons x v) ↔
          PowerBoundedEval s p (cons x (fun j => v (r j)))) := by
      intro x hx
      have hh := power_control_cons h i (Or.inl hx)
      have hh' : ∀ j, PowerQuantifierControl s (cons x v b.succ) p.depth
          (cons x v (powerBoundLift r j)) := by
        intro j
        change PowerQuantifierControl s (v b) p.depth ((fun l => cons x v (powerBoundLift r l)) j)
        rw [power_bound_lift_env]
        exact hh j
      simpa only [power_bound_lift_env] using hp (powerBoundLift r) b.succ (cons x v) hh'
    exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, hx, (step x hx).mp hp⟩,
      fun ⟨x, hx, hp⟩ => ⟨x, hx, (step x hx).mpr hp⟩⟩
  | allMem i p hp =>
    have step : ∀ x, s x (v (r i)) →
        (BoundedEval s (p.restrict (powerBoundLift r) b.succ) (cons x v) ↔
          PowerBoundedEval s p (cons x (fun j => v (r j)))) := by
      intro x hx
      have hh := power_control_cons h i (Or.inl hx)
      have hh' : ∀ j, PowerQuantifierControl s (cons x v b.succ) p.depth
          (cons x v (powerBoundLift r j)) := by
        intro j
        change PowerQuantifierControl s (v b) p.depth ((fun l => cons x v (powerBoundLift r l)) j)
        rw [power_bound_lift_env]
        exact hh j
      simpa only [power_bound_lift_env] using hp (powerBoundLift r) b.succ (cons x v) hh'
    exact ⟨fun H x hx => (step x hx).mp (H x hx), fun H x hx => (step x hx).mpr (H x hx)⟩
  | exSubset i p hp =>
    have step : ∀ x, Subset s x (v (r i)) →
        (BoundedEval s (p.restrict (powerBoundLift r) b.succ) (cons x v) ↔
          PowerBoundedEval s p (cons x (fun j => v (r j)))) := by
      intro x hx
      have hh := power_control_cons h i (Or.inr hx)
      have hh' : ∀ j, PowerQuantifierControl s (cons x v b.succ) p.depth
          (cons x v (powerBoundLift r j)) := by
        intro j
        change PowerQuantifierControl s (v b) p.depth ((fun l => cons x v (powerBoundLift r l)) j)
        rw [power_bound_lift_env]
        exact hh j
      simpa only [power_bound_lift_env] using hp (powerBoundLift r) b.succ (cons x v) hh'
    change (∃ x, s x (v b) ∧ (Subset s x (v (r i)) ∧
      BoundedEval s (p.restrict (powerBoundLift r) b.succ) (cons x v))) ↔ _
    exact ⟨fun ⟨x, _, hx, hp⟩ => ⟨x, hx, (step x hx).mp hp⟩,
      fun ⟨x, hx, hp⟩ => ⟨x, (h i x (Or.inr hx)).1, hx, (step x hx).mpr hp⟩⟩
  | allSubset i p hp =>
    have step : ∀ x, Subset s x (v (r i)) →
        (BoundedEval s (p.restrict (powerBoundLift r) b.succ) (cons x v) ↔
          PowerBoundedEval s p (cons x (fun j => v (r j)))) := by
      intro x hx
      have hh := power_control_cons h i (Or.inr hx)
      have hh' : ∀ j, PowerQuantifierControl s (cons x v b.succ) p.depth
          (cons x v (powerBoundLift r j)) := by
        intro j
        change PowerQuantifierControl s (v b) p.depth ((fun l => cons x v (powerBoundLift r l)) j)
        rw [power_bound_lift_env]
        exact hh j
      simpa only [power_bound_lift_env] using hp (powerBoundLift r) b.succ (cons x v) hh'
    change (∀ x, s x (v b) → Subset s x (v (r i)) →
      BoundedEval s (p.restrict (powerBoundLift r) b.succ) (cons x v)) ↔ _
    exact ⟨fun H x hx => (step x hx).mp (H x (h i x (Or.inr hx)).1 hx),
      fun H x _ hx => (step x hx).mpr (H x hx)⟩

#print axioms power_bounded_restrict_correct
end FullBridge
