import GlobalLeastQuotient
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem pruned_edges_are_members (b : U) :
    ∀ x y, FormulaEdges s prunedMemberFormula (cons b Fin.elim0) x y → s y x :=
  fun _ _ h => h.2.2

abbrev PrunedQuotient (base : BaseCollection s) (b : U) :=
  LeastGlobalQuotient base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b)
abbrev prunedCode (base : BaseCollection s) (b : U) :=
  leastGlobalCode base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b)
abbrev prunedMember (base : BaseCollection s) (b : U) :=
  leastGlobalMember base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b)

theorem pruned_excluded_empty (base : BaseCollection s) {b x z : U}
    (hx : s b x) (hz : ∀ y, ¬s y z) : prunedCode base b x = prunedCode base b z := by
  apply (least_global_code_eq base _ _ _ x z).mpr
  apply (defined_least_fixed base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b) x z).mpr
  constructor
  · intro y hy
    exact False.elim (hy.1 hx)
  · intro y hy
    exact False.elim (hz y hy.2.2)

/-- Every class has a representative in the retained carrier, without AC. -/
theorem pruned_good_representative (base : BaseCollection s) (b : U) (X : PrunedQuotient base b) :
    ∃ x, ¬s b x ∧ prunedCode base b x = X := by
  classical
  obtain ⟨x, rfl⟩ := least_global_code_onto base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b) X
  by_cases hx : s b x
  · obtain ⟨z, hz⟩ := base.empty
    exact ⟨z, hz b, (pruned_excluded_empty base hx hz).symm⟩
  · exact ⟨x, hx, rfl⟩

/-- The self-member premise is sufficient; a full self-singleton premise is unnecessary. -/
theorem pruned_good_row (base : BaseCollection s) {b a : U} (hbb : s b b)
    (ha : ∀ x, s x a → ¬s b x) :
    ¬s b a ∧ ∀ X, prunedMember base b X (prunedCode base b a) ↔
      ∃ x, s x a ∧ prunedCode base b x = X := by
  have hba : ¬s b a := fun h => ha b h hbb
  refine ⟨hba, ?_⟩
  intro X
  refine (least_global_exact_members base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b) a X).trans ?_
  constructor
  · rintro ⟨x, hx, hq⟩
    exact ⟨x, hx.2.2, hq⟩
  · rintro ⟨x, hx, hq⟩
    exact ⟨x, ⟨hba, ha x hx, hx⟩, hq⟩

/-- Replace excluded members by one empty representative, collecting an actual
    source set of retained representatives with the same image of its members. -/
theorem pruned_normalized_image (base : BaseCollection s) (b a : U) :
    ∃ c, (∀ x, s x c → ¬s b x) ∧ ∀ X,
      (∃ x, s x c ∧ prunedCode base b x = X) ↔ (∃ x, s x a ∧ prunedCode base b x = X) := by
  classical
  obtain ⟨c, hc⟩ := base.separation 1 (.impl (.member 1 0) .bottom) (cons b Fin.elim0) a
  have hc' : ∀ x, s x c ↔ s x a ∧ ¬s b x := hc
  by_cases bad : ∃ x, s x a ∧ s b x
  · obtain ⟨z, hz⟩ := base.empty
    obtain ⟨one, hone⟩ := base.pairing z z
    obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union c one
    have hd' : ∀ x, s x d ↔ s x c ∨ x = z := by
      intro x
      rw [hd x, hone x]
      exact ⟨fun h => h.elim Or.inl (fun h => Or.inr (h.elim id id)),
        fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
    refine ⟨d, ?_, ?_⟩
    · intro x hx
      rcases (hd' x).mp hx with hcX | rfl
      · exact ((hc' x).mp hcX).2
      · exact hz b
    · intro X
      constructor
      · rintro ⟨x, hx, hq⟩
        rcases (hd' x).mp hx with hcX | rfl
        · exact ⟨x, ((hc' x).mp hcX).1, hq⟩
        · obtain ⟨y, hya, hby⟩ := bad
          exact ⟨y, hya, (pruned_excluded_empty base hby hz).trans hq⟩
      · rintro ⟨x, hxa, hq⟩
        by_cases hbx : s b x
        · exact ⟨z, (hd' z).mpr (Or.inr rfl), (pruned_excluded_empty base hbx hz).symm.trans hq⟩
        · exact ⟨x, (hd' x).mpr (Or.inl ((hc' x).mpr ⟨hxa, hbx⟩)), hq⟩
  · refine ⟨c, fun x hx => ((hc' x).mp hx).2, ?_⟩
    intro X
    constructor
    · rintro ⟨x, hx, hq⟩
      exact ⟨x, ((hc' x).mp hx).1, hq⟩
    · rintro ⟨x, hx, hq⟩
      exact ⟨x, (hc' x).mpr ⟨hx, fun hb => bad ⟨x, hx, hb⟩⟩, hq⟩

/-- Every source-set-sized image is an actual row of the quotient. -/
theorem pruned_row_realization (base : BaseCollection s) {b : U} (hbb : s b b) (a : U) :
    ∃ c, ¬s b c ∧ ∀ X, prunedMember base b X (prunedCode base b c) ↔
      ∃ x, s x a ∧ prunedCode base b x = X := by
  obtain ⟨c, hc, hi⟩ := pruned_normalized_image base b a
  obtain ⟨hbc, hrow⟩ := pruned_good_row base hbb hc
  exact ⟨c, hbc, fun X => (hrow X).trans (hi X)⟩

theorem pruned_quotient_empty (base : BaseCollection s) (b : U) : Empty (prunedMember base b) := by
  obtain ⟨z, hz⟩ := base.empty
  refine ⟨prunedCode base b z, ?_⟩
  intro X hX
  obtain ⟨x, hx, _⟩ := (least_global_exact_members base prunedMemberFormula
    (cons b Fin.elim0) (pruned_edges_are_members b) z X).mp hX
  exact hz x hx.2.2

theorem pruned_quotient_pairing (base : BaseCollection s) {b : U} (hbb : s b b) :
    Pairing (prunedMember base b) := by
  intro X Y
  obtain ⟨x, _, rfl⟩ := pruned_good_representative base b X
  obtain ⟨y, _, rfl⟩ := pruned_good_representative base b Y
  obtain ⟨a, ha⟩ := base.pairing x y
  obtain ⟨c, _, hc⟩ := pruned_row_realization base hbb a
  refine ⟨prunedCode base b c, ?_⟩
  intro Z
  rw [hc Z]
  constructor
  · rintro ⟨z, hz, hq⟩
    rcases (ha z).mp hz with rfl | rfl
    · exact Or.inl hq.symm
    · exact Or.inr hq.symm
  · intro h
    rcases h with rfl | rfl
    · exact ⟨x, (ha x).mpr (Or.inl rfl), rfl⟩
    · exact ⟨y, (ha y).mpr (Or.inr rfl), rfl⟩

#print axioms pruned_row_realization
#print axioms pruned_quotient_pairing
end FullBridge
