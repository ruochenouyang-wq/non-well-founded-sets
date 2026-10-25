import QuineDomainSwaps
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem elementary_map_pair {j : U → U} (hj : ElementaryMap s s j) {c l r : U}
    (hc : IsPair s c l r) : IsPair s (j c) (j l) (j r) := by
  have h := hj (pairFormula (n := 3) 0 1 2) (cons c (cons l (cons r Fin.elim0)))
  rw [eval_pairFormula, eval_pairFormula] at h
  exact h.mp hc

theorem elementary_map_fixed_members_set (base : BaseCollection s) {j : U → U}
    (hj : ElementaryMap s s j) (ho : ∀ y, ∃ x, j x = y) {a : U}
    (ha : ∀ x, s x a → j x = x) : j a = a := by
  have hm : ∀ x y, s x y ↔ s (j x) (j y) := fun x y => by
    exact hj (Formula.member (n := 2) 0 1) (cons x (cons y Fin.elim0))
  apply base.extensional
  intro y
  obtain ⟨x, rfl⟩ := ho y
  constructor
  · intro hy
    have hx := (hm x a).mpr hy
    exact (ha x hx).symm ▸ hx
  · intro hy
    have hfix := ha (j x) hy
    have he := elementary_map_injective hj (j x) x hfix
    exact (hm x a).mp (he ▸ hy)

theorem pair_swap_moves_internal_choice {a c l r f : U} {j : U → U}
    (hj : ElementaryMap s s j) (hc : s c a) (hp : IsPair s c l r) (hne : l ≠ r)
    (hfix : j c = c) (hl : j l = r) (hr : j r = l) (hf : ChoiceFunctionCode s a f) : j f ≠ f := by
  intro he
  obtain ⟨y, hcy, hu⟩ := hf.1.2 c hc
  have hrel := (elementary_map_coded_relation hj f c y).mp hcy
  rw [he, hfix] at hrel
  have hy := hu (j y) hrel
  rcases (hp y).mp (hf.2 c hc y hcy) with h | h
  · rw [h, hl] at hy
    exact hne hy.symm
  · rw [h, hr] at hy
    exact hne hy

/-- Every selected row has a full-model involution swapping its labels,
    fixing all other labels and every row of this one internal family. These
    individual extensions are not asserted to commute or be eventually fixed. -/
theorem countable_bafa_internal_pair_swap (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) {a : U}
    (P : InternalQuinePairs s a) {x l r : U}
    (hl : CodedRelation s P.leftCode x l) (hr : CodedRelation s P.rightCode x r) :
    ∃ j : U → U, ElementaryMap s s j ∧ (∀ y, ∃ z, j z = y) ∧ (∀ y, j (j y) = y) ∧
      LocallyInternalTransitiveMap s j ∧ j l = r ∧ j r = l ∧
      (∀ c, s c P.family → j c = c) ∧ j P.family = P.family ∧
      (∀ c y, s c P.family → s y c → y ≠ l → y ≠ r → j y = y) ∧
      (∀ y, internalCode base (j y) = internalCode base y) ∧
      (∀ f, ChoiceFunctionCode s P.family f → j f ≠ f) := by
  classical
  obtain ⟨c, hc⟩ := base.pairing l r
  have hcf := (P.members c).mpr ⟨x, l, r, coded_function_domain P.leftFunction hl, hl, hr, hc⟩
  obtain ⟨d, hd⟩ := base.union P.family
  have hld := (hd l).mpr ⟨c, hcf, (hc l).mpr (Or.inl rfl)⟩
  have hrd := (hd r).mpr ⟨c, hcf, (hc r).mpr (Or.inr rfl)⟩
  have hquines : ∀ y, s y d → SelfSingleton s y := by
    intro y hy
    obtain ⟨b, hb, hyb⟩ := (hd y).mp hy
    obtain ⟨i, L, R, _, hL, hR, hb⟩ := (P.members b).mp hb
    rcases (hb y).mp hyb with rfl | rfl
    · exact P.leftQuine i _ hL
    · exact P.rightQuine i _ hR
  have hne := internal_quine_pair_distinct P hl hr
  obtain ⟨j, hj, ho, hs, hlocal, hswap, hq⟩ :=
    countable_bafa_quine_domain_swap base hB enum henum hquines hld hrd hne
  have hjl : j l = r := by simpa [quineSwap] using hswap l hld
  have hjr : j r = l := by simpa [quineSwap, Ne.symm hne] using hswap r hrd
  have hother : ∀ b y, s b P.family → s y b → y ≠ l → y ≠ r → j y = y := by
    intro b y hb hy hyl hyr
    simpa [quineSwap, hyl, hyr] using hswap y ((hd y).mpr ⟨b, hb, hy⟩)
  have hrows : ∀ b, s b P.family → j b = b := by
    intro b hbf
    obtain ⟨i, L, R, _, hL, hR, hb⟩ := (P.members b).mp hbf
    have hbj := elementary_map_pair hj hb
    by_cases hix : i = x
    · subst i
      have hLl := coded_function_value_unique P.leftFunction hL hl
      have hRr := coded_function_value_unique P.rightFunction hR hr
      subst L; subst R
      rw [hjl, hjr] at hbj
      exact pair_unique base.extensional hbj (fun y => (hb y).trans or_comm)
    · have hLl : L ≠ l := fun he => hix (P.leftInjective i x l (he ▸ hL) hl)
      have hLr : L ≠ r := fun he => P.disjoint i x r (he ▸ hL) hr
      have hRl : R ≠ l := fun he => P.disjoint x i l hl (he ▸ hR)
      have hRr : R ≠ r := fun he => hix (P.rightInjective i x r (he ▸ hR) hr)
      have hJL := hother b L hbf ((hb L).mpr (Or.inl rfl)) hLl hLr
      have hJR := hother b R hbf ((hb R).mpr (Or.inr rfl)) hRl hRr
      rw [hJL, hJR] at hbj
      exact pair_unique base.extensional hbj hb
  exact ⟨j, hj, ho, hs, hlocal, hjl, hjr, hrows, elementary_map_fixed_members_set base hj ho hrows,
    hother, hq, fun f hf => pair_swap_moves_internal_choice hj hcf hc hne (hrows c hcf) hjl hjr hf⟩

#print axioms countable_bafa_internal_pair_swap
end FullBridge
