import BoundedSyntax
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem eventually_fixed_finite_parameters {swap : Nat → U → U} {n}
    (v : Fin n → U) (hv : ∀ i, EventuallyFixedBy swap (v i)) :
    ∃ N, ∀ k, N ≤ k → ∀ i, swap k (v i) = v i := by
  induction n with
  | zero => exact ⟨0, fun _ _ i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨N, hN⟩ := hv 0
    obtain ⟨M, hM⟩ := ih (fun i => v i.succ) (fun i => hv i.succ)
    refine ⟨max N M, fun k hk i => ?_⟩
    exact Fin.cases (hN k (Nat.le_trans (Nat.le_max_left N M) hk))
      (fun j => hM k (Nat.le_trans (Nat.le_max_right N M) hk) j) i

theorem elementary_map_separation_set (base : BaseCollection s) {j : U → U}
    (hj : ElementaryMap s s j) (ho : ∀ y, ∃ x, j x = y) {n} (p : Formula (n+1))
    (v : Fin n → U) {a b : U} (hb : ∀ x, s x b ↔ s x a ∧ Eval s p (cons x v))
    (ha : j a = a) (hv : ∀ i, j (v i) = v i) : j b = b := by
  have hm : ∀ x y, s x y ↔ s (j x) (j y) := fun x y => by
    exact hj (Formula.member (n := 2) 0 1) (cons x (cons y Fin.elim0))
  apply base.extensional
  intro y
  obtain ⟨x, rfl⟩ := ho y
  have he : (fun i => j (cons x v i)) = cons (j x) v := by
    funext i
    exact Fin.cases rfl (fun k => hv k) i
  have hp := hj p (cons x v)
  rw [he] at hp
  rw [← hm x b, hb x, hb (j x)]
  exact and_congr (by simpa only [ha] using hm x a) hp

/-- Source semantics are explicitly retained here: this is closure under
    ambient definable subsets, not full Separation for the subtype's truth. -/
theorem hereditary_support_source_separation (base : BaseCollection s) {swap : Nat → U → U}
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {n} (p : Formula (n+1)) (v : Fin n → U) {a b : U}
    (ha : HereditarilyEventuallyFixed s swap a)
    (hv : ∀ i, HereditarilyEventuallyFixed s swap (v i))
    (hb : ∀ x, s x b ↔ s x a ∧ Eval s p (cons x v)) : HereditarilyEventuallyFixed s swap b := by
  apply hereditary_support_intro
  · obtain ⟨N, hN⟩ := hereditary_support_root ha
    obtain ⟨M, hM⟩ := eventually_fixed_finite_parameters v (fun i => hereditary_support_root (hv i))
    exact ⟨max N M, fun k hk => elementary_map_separation_set base (hj k) (ho k) p v hb
      (hN k (Nat.le_trans (Nat.le_max_left N M) hk))
      (hM k (Nat.le_trans (Nat.le_max_right N M) hk))⟩
  · exact fun x hx => hereditary_support_member ha ((hb x).mp hx).1

theorem supported_carrier_bounded_separation (base : BaseCollection s) (swap : Nat → U → U)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y) :
    BoundedSeparation (supportedMember (s := s) swap) := by
  intro n p v a
  obtain ⟨b, hb⟩ := base.separation n p.toFormula (fun i => (v i).val) a.val
  have hB := hereditary_support_source_separation base hj ho p.toFormula (fun i => (v i).val)
    a.property (fun i => (v i).property) hb
  refine ⟨⟨b, hB⟩, fun x => ?_⟩
  have hsem := (bounded_eval_toFormula (s := s) p (cons x.val (fun i => (v i).val))).trans
    (by simpa only [supported_cons_values] using (supported_bounded_absoluteness p (cons x v)).symm)
  exact (hb x.val).trans (and_congr Iff.rfl hsem)

/-- An actual candidate satisfying the full bounded Separation scheme. -/
theorem countable_bafa_supported_bounded_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ F, ∃ S : PairSwapSequence s F,
      HereditarilyEventuallyFixed s S.map F ∧
      Extensional (supportedMember (s := s) S.map) ∧ Empty (supportedMember (s := s) S.map) ∧
      Pairing (supportedMember (s := s) S.map) ∧ Union (supportedMember (s := s) S.map) ∧
      Infinity (supportedMember (s := s) S.map) ∧ BoundedSeparation (supportedMember (s := s) S.map) ∧
      ¬ ChoiceCode (supportedMember (s := s) S.map) := by
  obtain ⟨F, S, hF, he, hz, hp, hu, hi, hn⟩ := countable_bafa_supported_infinite_candidate base hB enum henum
  exact ⟨F, S, hF, he, hz, hp, hu, hi, supported_carrier_bounded_separation base S.map
    (fun n => (S.action n).elementary) (fun n => (S.action n).onto), hn⟩

#print axioms countable_bafa_supported_bounded_candidate
end FullBridge
