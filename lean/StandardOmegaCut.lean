import SupportedFixedRowsPowers
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem standard_omega_members (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (k : Nat) (x : U) :
    s x (standardOmegaValue base z k) ↔ ∃ j, j < k ∧ x = standardOmegaValue base z j := by
  induction k with
  | zero =>
    constructor
    · exact fun h => False.elim (hw.1 x h)
    · rintro ⟨j, hj, _⟩
      exact False.elim (Nat.not_lt_zero j hj)
  | succ k ih =>
    have hs : IsSuccessor s (standardOmegaValue base z k) (standardOmegaValue base z (k+1)) :=
      Classical.choose_spec (successor_exists base _)
    rw [hs x, ih]
    constructor
    · rintro (⟨j, hj, hx⟩ | hx)
      · exact ⟨j, Nat.lt_trans hj (Nat.lt_succ_self k), hx⟩
      · exact ⟨k, Nat.lt_succ_self k, hx⟩
    · rintro ⟨j, hj, hx⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjk | rfl
      · exact Or.inl ⟨j, hjk, hx⟩
      · exact Or.inr hx

theorem internal_omega_zero_or_contains_zero (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) : ∀ x, s x w → x = z ∨ s z x := by
  let p : Formula 2 := (Formula.equal 0 1).disj (.member 1 0)
  have hev : ∀ x, Eval s p (cons x (cons z Fin.elim0)) ↔ x = z ∨ s z x := by
    intro x
    simp only [p, eval_disj, Eval]
    rfl
  have h := internal_omega_formula_induction base hw p (cons z Fin.elim0)
    ((hev z).mpr (Or.inl rfl)) (by
      intro x _ hx y hxy
      apply (hev y).mpr
      apply Or.inr
      rcases (hev x).mp hx with heq | hz
      · exact (hxy z).mpr (Or.inr heq.symm)
      · exact (hxy z).mpr (Or.inl hz))
  exact fun x hx => (hev x).mp (h x hx)

theorem internal_omega_no_successor_gap (base : BaseCollection s) {z w a b : U}
    (hw : OmegaCode s z w) (hab : IsSuccessor s a b) :
    ∀ x, s x w → s a x → x = b ∨ s b x := by
  let p : Formula 3 := .impl (.member 1 0) ((Formula.equal 0 2).disj (.member 2 0))
  have hev : ∀ x, Eval s p (cons x (cons a (cons b Fin.elim0))) ↔ (s a x → x = b ∨ s b x) := by
    intro x
    simp only [p, Eval, eval_disj]
    rfl
  have h := internal_omega_formula_induction base hw p (cons a (cons b Fin.elim0))
    ((hev z).mpr (fun haz => False.elim (hw.1 a haz))) (by
      intro x _ hx y hxy
      apply (hev y).mpr
      intro hay
      rcases (hxy a).mp hay with hax | hax
      · apply Or.inr
        rcases (hev x).mp hx hax with heq | hbx
        · exact (hxy b).mpr (Or.inr heq.symm)
        · exact (hxy b).mpr (Or.inl hbx)
      · subst x
        exact Or.inl (successor_unique base.extensional hxy hab))
  exact fun x hx => (hev x).mp (h x hx)

theorem nonstandard_omega_contains_all_standard (base : BaseCollection s) {z w a : U}
    (hw : OmegaCode s z w) (ha : s a w)
    (hns : ∀ n, a ≠ standardOmegaValue base z n) :
    ∀ n, s (standardOmegaValue base z n) a := by
  intro n
  induction n with
  | zero => exact (internal_omega_zero_or_contains_zero base hw a ha).resolve_left (hns 0)
  | succ n ih =>
    have hs : IsSuccessor s (standardOmegaValue base z n) (standardOmegaValue base z (n+1)) :=
      Classical.choose_spec (successor_exists base _)
    exact (internal_omega_no_successor_gap base hw hs a ha ih).resolve_left (hns (n+1))

/-- A proper external standard cut cannot be the extension of a source
    set: such a set would be inductive and hence contain internal omega. -/
theorem standard_omega_cut_not_internal (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w)
    (hns : ∃ a, s a w ∧ ∀ n, a ≠ standardOmegaValue base z n) :
    ¬ ∃ c, ∀ x, s x c ↔ ∃ n, x = standardOmegaValue base z n := by
  rintro ⟨c, hc⟩
  have hci : InductiveCode s z c := by
    refine ⟨(hc z).mpr ⟨0, rfl⟩, ?_⟩
    intro x hx y hxy
    obtain ⟨n, rfl⟩ := (hc x).mp hx
    apply (hc y).mpr
    refine ⟨n+1, ?_⟩
    exact successor_unique base.extensional hxy (Classical.choose_spec (successor_exists base _))
  obtain ⟨a, haw, ha⟩ := hns
  obtain ⟨n, hn⟩ := (hc a).mp (hw.2.2 c hci a haw)
  exact ha n hn

#print axioms standard_omega_cut_not_internal
end FullBridge
