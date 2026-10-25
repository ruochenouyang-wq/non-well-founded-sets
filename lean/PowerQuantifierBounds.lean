import PowerBoundedSyntax
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem power_control_bound_mono {B C : U} (hBC : Subset s B C) (n : Nat) {x : U}
    (h : PowerQuantifierControl s B n x) : PowerQuantifierControl s C n x := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih =>
    intro y hy
    exact ⟨hBC y (h y hy).1, ih (h y hy).2⟩

theorem power_control_depth_mono {B x : U} {k n : Nat} (hkn : k ≤ n)
    (h : PowerQuantifierControl s B n x) : PowerQuantifierControl s B k x := by
  induction k generalizing n x with
  | zero => trivial
  | succ k ih =>
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hkn)
    | succ n =>
      intro y hy
      exact ⟨(h y hy).1, ih (Nat.le_of_succ_le_succ hkn) (h y hy).2⟩

/-- A single source set bounds both kinds of next quantifier value. -/
theorem power_quantifier_step_bound (hp : Pairing s) (hu : Union s) (hpow : PowerSet s) (d : U) :
    ∃ e, Subset s d e ∧ ∀ x, s x d → ∀ y, (s y x ∨ Subset s y x) → s y e := by
  obtain ⟨a, ha⟩ := hu d
  obtain ⟨p, hP⟩ := hpow a
  obtain ⟨c, hc⟩ := binary_union_exists hp hu a p
  obtain ⟨e, he⟩ := binary_union_exists hp hu d c
  refine ⟨e, fun x hx => (he x).mpr (Or.inl hx), fun x hx y hy => (he y).mpr (Or.inr ?_)⟩
  rcases hy with hym | hys
  · exact (hc y).mpr (Or.inl ((ha y).mpr ⟨x, hx, hym⟩))
  · exact (hc y).mpr (Or.inr ((hP y).mpr (fun z hz => (ha z).mpr ⟨x, hx, hys z hz⟩)))

theorem power_quantifier_control_exists (hp : Pairing s) (hu : Union s) (hpow : PowerSet s)
    (d : U) (n : Nat) : ∃ B, ∀ x, s x d → PowerQuantifierControl s B n x := by
  induction n generalizing d with
  | zero => exact ⟨d, fun _ _ => True.intro⟩
  | succ n ih =>
    obtain ⟨e, _, he⟩ := power_quantifier_step_bound hp hu hpow d
    obtain ⟨B, hB⟩ := ih e
    obtain ⟨C, hC⟩ := binary_union_exists hp hu e B
    refine ⟨C, fun x hx y hy => ?_⟩
    have hey := he x hx y hy
    exact ⟨(hC y).mpr (Or.inl hey),
      power_control_bound_mono (fun z hz => (hC z).mpr (Or.inr hz)) n (hB y hey)⟩

theorem power_finite_environment_bound (hp : Pairing s) (hu : Union s) {n}
    (a : U) (v : Fin n → U) : ∃ d, Subset s a d ∧ ∀ i, s (v i) d := by
  induction n with
  | zero => exact ⟨a, fun _ h => h, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨d, had, hd⟩ := ih (fun i => v i.succ)
    obtain ⟨p, hP⟩ := hp (v 0) (v 0)
    obtain ⟨e, he⟩ := binary_union_exists hp hu p d
    refine ⟨e, fun x hx => (he x).mpr (Or.inr (had x hx)), fun i => ?_⟩
    exact Fin.cases ((he (v 0)).mpr (Or.inl ((hP (v 0)).mpr (Or.inl rfl))))
      (fun j => (he (v j.succ)).mpr (Or.inr (hd j))) i

#print axioms power_quantifier_control_exists
#print axioms power_finite_environment_bound
end FullBridge
