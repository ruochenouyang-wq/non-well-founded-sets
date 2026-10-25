import InternalPairChoice
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

noncomputable def quineSwap (u v x : U) : U := by
  classical
  exact if x = u then v else if x = v then u else x

def quineSwapFormula {n} (u v x y : Fin n) : Formula n :=
  ((Formula.equal x u).conj (.equal y v)).disj
    (((Formula.equal x v).conj (.equal y u)).disj
      ((Formula.impl (.equal x u) .bottom).conj ((Formula.impl (.equal x v) .bottom).conj (.equal y x))))

theorem eval_quineSwapFormula {n} (u v x y : Fin n) (e : Fin n → U) (hne : e u ≠ e v) :
    Eval s (quineSwapFormula u v x y) e ↔ e y = quineSwap (e u) (e v) (e x) := by
  classical
  simp only [quineSwapFormula, eval_disj, Eval]
  by_cases hx : e x = e u
  · simp [hx, hne, quineSwap]
  · by_cases hv : e x = e v
    · simp [hv, Ne.symm hne, quineSwap]
    · simp [hx, hv, quineSwap]

theorem quine_swap_involutive {u v : U} (hne : u ≠ v) (x : U) :
    quineSwap u v (quineSwap u v x) = x := by
  classical
  by_cases hx : x = u
  · simp [hx, quineSwap, Ne.symm hne]
  · by_cases hv : x = v
    · simp [hv, quineSwap, Ne.symm hne]
    · simp [quineSwap, hx, hv]

/-- Swap two specified quines on an entire internal quine set, fixing every
    other member. The full local involution graph is a source set. -/
theorem quine_domain_internal_swap (base : BaseCollection s) {a u v : U}
    (ha : ∀ x, s x a → SelfSingleton s x) (hu : s u a) (hv : s v a) (hne : u ≠ v) :
    ∃ P : TransitiveInvolution s, P.domain = a ∧
      ∀ x y, CodedRelation s P.code x y ↔ s x a ∧ y = quineSwap u v x := by
  classical
  let j := quineSwap u v
  have hs : ∀ x, j (j x) = x := quine_swap_involutive hne
  have hmem : ∀ x, s x a → s (j x) a := by
    intro x hx
    by_cases hxu : x = u
    · simpa [j, quineSwap, hxu] using hv
    · by_cases hxv : x = v
      · simpa [j, quineSwap, hxv, Ne.symm hne] using hu
      · simpa [j, quineSwap, hxu, hxv] using hx
  have hinj : ∀ x y, j x = j y → x = y := by
    intro x y h
    exact (hs x).symm.trans ((congrArg j h).trans (hs y))
  obtain ⟨p, hpG, hp⟩ := normalized_relation_comprehension base
    (quineSwapFormula (n := 4) 2 3 1 0) (cons u (cons v Fin.elim0)) a
  have hrel : ∀ x y, CodedRelation s p x y ↔ s x a ∧ y = j x := by
    intro x y
    have he := eval_quineSwapFormula (s := s) (n := 4) 2 3 1 0
      (cons y (cons x (cons u (cons v Fin.elim0)))) hne
    have hh := (hp x y).trans (and_congr Iff.rfl (and_congr Iff.rfl he))
    exact hh.trans ⟨fun h => ⟨h.1, h.2.2⟩, fun ⟨hx, heq⟩ => ⟨hx, heq.symm ▸ hmem x hx, heq⟩⟩
  have hf : FunctionCode s a p := by
    constructor
    · intro z hz
      obtain ⟨x, y, hx, _, hxy⟩ := hpG z hz
      exact ⟨x, y, hx, hxy⟩
    · intro x hx
      exact ⟨j x, (hrel x _).mpr ⟨hx, rfl⟩, fun y hy => ((hrel x y).mp hy).2⟩
  have hsym : ∀ x y, CodedRelation s p x y → CodedRelation s p y x := by
    intro x y hxy
    obtain ⟨hx, rfl⟩ := (hrel x y).mp hxy
    exact (hrel _ _).mpr ⟨hmem x hx, (hs x).symm⟩
  have hIso : MembershipIsoCode s a a p := by
    refine ⟨hf, ?_, ?_, ?_⟩
    · intro x y z hxz hyz
      exact hinj x y (((hrel x z).mp hxz).2.symm.trans ((hrel y z).mp hyz).2)
    · intro y
      constructor
      · intro hy
        exact ⟨j y, hmem y hy, (hrel _ _).mpr ⟨hmem y hy, (hs y).symm⟩⟩
      · rintro ⟨x, _, hxy⟩
        obtain ⟨hx, rfl⟩ := (hrel x y).mp hxy
        exact hmem x hx
    · intro x y X Y hxX hyY
      obtain ⟨hx, rfl⟩ := (hrel x X).mp hxX
      obtain ⟨hy, rfl⟩ := (hrel y Y).mp hyY
      rw [ha x hx y, ha (j x) (hmem x hx) (j y)]
      exact ⟨congrArg j, hinj y x⟩
  have hTrans : TransitiveCode s a := fun x hx y hy => ((ha x hx y).mp hy).symm ▸ hx
  exact ⟨⟨a, p, hTrans, hIso, hsym⟩, rfl, hrel⟩

theorem countable_bafa_quine_domain_swap (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) {a u v : U}
    (ha : ∀ x, s x a → SelfSingleton s x) (hu : s u a) (hv : s v a) (hne : u ≠ v) :
    ∃ j : U → U, ElementaryMap s s j ∧ (∀ y, ∃ x, j x = y) ∧ (∀ x, j (j x) = x) ∧
      LocallyInternalTransitiveMap s j ∧ (∀ x, s x a → j x = quineSwap u v x) ∧
      (∀ x, internalCode base (j x) = internalCode base x) := by
  obtain ⟨P, _, hp⟩ := quine_domain_internal_swap base ha hu hv hne
  obtain ⟨j, hj, ho, hs, hl, he, hq, _⟩ := countable_bafa_involution_extension base hB enum henum P
  exact ⟨j, hj, ho, hs, hl, fun x hx => he x _ ((hp x _).mpr ⟨hx, rfl⟩), hq⟩

#print axioms countable_bafa_quine_domain_swap
end FullBridge
