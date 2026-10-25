import QuotientStability
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- External data for a conditional symmetry argument. The natural-number indexing,
    automorphisms, and eventual fixation are hypotheses, not internally constructed
    sets or a construction of a symmetric model. -/
structure PairSwapSystem (s : U → U → Prop) (a : U) where
  row : Nat → U
  left : Nat → U
  right : Nat → U
  swap : Nat → U → U
  row_mem : ∀ n, s (row n) a
  cover : ∀ x, s x a → ∃ n, x = row n
  pair_members : ∀ n y, s y (row n) ↔ y = left n ∨ y = right n
  distinct : ∀ n, left n ≠ right n
  injective : ∀ n x y, swap n x = swap n y → x = y
  onto : ∀ n y, ∃ x, swap n x = y
  membership : ∀ n x y, s x y ↔ s (swap n x) (swap n y)
  fix_row : ∀ n, swap n (row n) = row n
  swap_left : ∀ n, swap n (left n) = right n
  swap_right : ∀ n, swap n (right n) = left n
  eventually_fixed : ∀ f, ∃ N, ∀ n, N ≤ n → swap n f = f

theorem elementary_map_coded_relation {j : U → U}
    (hj : ElementaryMap s s j) (f x y : U) :
    CodedRelation s f x y ↔ CodedRelation s (j f) (j x) (j y) := by
  have h := hj (relatedFormula (n := 3) 2 1 0)
    (cons y (cons x (cons f Fin.elim0)))
  rw [eval_relatedFormula, eval_relatedFormula] at h
  exact h

/-- Every individual swap moves every putative internal choice function. -/
theorem pair_swap_moves_choice {a f : U} (P : PairSwapSystem s a)
    (hf : ChoiceFunctionCode s a f) (n : Nat) : P.swap n f ≠ f := by
  intro hfix
  obtain ⟨y, hy, huniq⟩ := hf.1.2 (P.row n) (P.row_mem n)
  have hm := hf.2 (P.row n) (P.row_mem n) y hy
  have hj : ElementaryMap s s (P.swap n) := bijective_membership_elementary (P.swap n)
    (P.injective n) (P.onto n) (P.membership n)
  have hrel := (elementary_map_coded_relation hj f (P.row n) y).mp hy
  rw [hfix, P.fix_row n] at hrel
  have hval := huniq (P.swap n y) hrel
  rcases (P.pair_members n y).mp hm with h | h
  · rw [h, P.swap_left n] at hval
    exact P.distinct n hval.symm
  · rw [h, P.swap_right n] at hval
    exact P.distinct n hval

theorem supported_pair_family_no_choice {a : U} (P : PairSwapSystem s a) :
    ¬ ∃ f, ChoiceFunctionCode s a f := by
  rintro ⟨f, hf⟩
  obtain ⟨N, hN⟩ := P.eventually_fixed f
  exact pair_swap_moves_choice P hf N (hN N (Nat.le_refl N))

theorem supported_pair_source_not_choice {a : U} (P : PairSwapSystem s a) :
    ¬ ChoiceCode s := by
  intro hAC
  apply supported_pair_family_no_choice P
  apply hAC a
  intro x hx
  obtain ⟨n, rfl⟩ := P.cover x hx
  exact ⟨P.left n, (P.pair_members n (P.left n)).mpr (Or.inl rfl)⟩

/-- Quine pairs collapse without assuming BAFA or any symmetry hypotheses. -/
theorem selfSingleton_pair_family_quotient_choice (base : BaseCollection s)
    {a : U} (row left right : Nat → U)
    (hmem : ∀ n, s (row n) a)
    (hcover : ∀ x, s x a → ∃ n, x = row n)
    (hp : ∀ n y, s y (row n) ↔ y = left n ∨ y = right n)
    (hl : ∀ n, SelfSingleton s (left n))
    (hr : ∀ n, SelfSingleton s (right n)) :
    internalCode base a = internalCode base (left 0) ∧
      ∃ F, ChoiceFunctionCode (internalMember base) (internalCode base a) F := by
  have heq : internalCode base a = internalCode base (left 0) := by
    apply constant_nonempty_family_code base ⟨row 0, hmem 0⟩ (hl 0)
    intro x hx
    obtain ⟨n, rfl⟩ := hcover x hx
    apply constant_nonempty_family_code base
      ⟨left n, (hp n (left n)).mpr (Or.inl rfl)⟩ (hl 0)
    intro y hy
    rcases (hp n y).mp hy with rfl | rfl
    · exact selfSingleton_same_code base (hl n) (hl 0)
    · exact selfSingleton_same_code base (hr n) (hl 0)
  refine ⟨heq, ?_⟩
  rw [heq]
  exact selfSingleton_has_choice (internal_base_model base) (selfSingleton_code base (hl 0))

/-- A conditional local separation criterion, not an existence theorem for the
    assumed full-model automorphisms or for a model of BAFA plus failure of AC. -/
theorem supported_quine_pairs_local_choice_loss (base : BaseCollection s)
    {a : U} (P : PairSwapSystem s a)
    (hl : ∀ n, SelfSingleton s (P.left n))
    (hr : ∀ n, SelfSingleton s (P.right n)) :
    (¬ ChoiceCode s) ∧ (¬ ∃ f, ChoiceFunctionCode s a f) ∧
      internalCode base a = internalCode base (P.left 0) ∧
      ∃ F, ChoiceFunctionCode (internalMember base) (internalCode base a) F := by
  exact ⟨supported_pair_source_not_choice P, supported_pair_family_no_choice P,
    selfSingleton_pair_family_quotient_choice base P.row P.left P.right
      P.row_mem P.cover P.pair_members hl hr⟩

#print axioms supported_quine_pairs_local_choice_loss
end FullBridge
