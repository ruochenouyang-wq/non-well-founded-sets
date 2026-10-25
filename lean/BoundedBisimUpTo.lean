import BoundedAugmentedBisim
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def BisimSandwich (s : U → U → Prop) (m r u v : U) : Prop :=
  ∃ x y, WithIdentity (CodedRelation s m) u x ∧ CodedRelation s r x y ∧
    WithIdentity (CodedRelation s m) y v

def bisimSandwichFormula : Formula 4 :=
  .ex (.ex (.conj (augmentedRelatedFormula 4 3 1)
    (.conj (relatedFormula 5 1 0) (augmentedRelatedFormula 4 0 2))))

theorem eval_bisimSandwichFormula (v u m r : U) :
    Eval s bisimSandwichFormula (cons v (cons u (cons m (cons r Fin.elim0)))) ↔
      BisimSandwich s m r u v := by
  simp only [bisimSandwichFormula, Eval, eval_augmentedRelatedFormula, eval_relatedFormula]
  rfl

theorem bisim_sandwich_absorb (base : BaseCollection s) {d m r u u' v v' : U}
    (hm : MaxAugmentedCode s d m)
    (hu : WithIdentity (CodedRelation s m) u u')
    (h : BisimSandwich s m r u' v')
    (hv : WithIdentity (CodedRelation s m) v' v) : BisimSandwich s m r u v := by
  obtain ⟨x, y, hux, hr, hyv⟩ := h
  exact ⟨x, y, maximal_augmented_trans base hm hu hux, hr,
    maximal_augmented_trans base hm hyv hv⟩

theorem bounded_bisimulation_up_to (base : BaseCollection s) {d m r : U}
    (hm : MaxAugmentedCode s d m) (hrG : GraphCode s d r)
    (hstep : ∀ x y, CodedRelation s r x y →
      (∀ u, s u x → ∃ v, s v y ∧ BisimSandwich s m r u v) ∧
      (∀ v, s v y → ∃ u, s u x ∧ BisimSandwich s m r u v)) :
    ∀ x y, CodedRelation s r x y → CodedRelation s m x y := by
  obtain ⟨w, hwG, hw⟩ := normalized_relation_comprehension base bisimSandwichFormula
    (cons m (cons r Fin.elim0)) d
  have hi : ∀ u v, CodedRelation s w u v ↔ BisimSandwich s m r u v := by
    intro u v
    have h := hw u v
    rw [eval_bisimSandwichFormula] at h
    constructor
    · intro hh
      exact (h.mp hh).2.2
    · intro hh
      obtain ⟨x, y, hux, hrxy, hyv⟩ := hh
      have hb := graphCode_endpoints hrG hrxy
      have hu : s u d := hux.elim (fun heq => heq ▸ hb.1) (fun hrel => (graphCode_endpoints hm.1 hrel).1)
      have hv : s v d := hyv.elim (fun heq => heq ▸ hb.2) (fun hrel => (graphCode_endpoints hm.1 hrel).2)
      exact h.mpr ⟨hu, hv, x, y, hux, hrxy, hyv⟩
  have hwB : Bisimulation s (WithIdentity (CodedRelation s w)) := by
    intro u v huv
    rcases huv with rfl | huv
    · exact ⟨fun z hz => ⟨z, hz, Or.inl rfl⟩, fun z hz => ⟨z, hz, Or.inl rfl⟩⟩
    obtain ⟨x, y, hux, hrxy, hyv⟩ := (hi u v).mp huv
    have hleft := hm.2.1 u x hux
    have hright := hm.2.1 y v hyv
    have hmiddle := hstep x y hrxy
    constructor
    · intro u' hu'
      obtain ⟨x', hx', hux'⟩ := hleft.1 u' hu'
      obtain ⟨y', hy', hs⟩ := hmiddle.1 x' hx'
      obtain ⟨v', hv', hyv'⟩ := hright.1 y' hy'
      exact ⟨v', hv', Or.inr ((hi u' v').mpr (bisim_sandwich_absorb base hm hux' hs hyv'))⟩
    · intro v' hv'
      obtain ⟨y', hy', hyv'⟩ := hright.2 v' hv'
      obtain ⟨x', hx', hs⟩ := hmiddle.2 y' hy'
      obtain ⟨u', hu', hux'⟩ := hleft.2 x' hx'
      exact ⟨u', hu', Or.inr ((hi u' v').mpr (bisim_sandwich_absorb base hm hux' hs hyv'))⟩
  intro x y hxy
  exact hm.2.2 w hwG hwB x y ((hi x y).mpr ⟨x, y, Or.inl rfl, hxy, Or.inl rfl⟩)

#print axioms bounded_bisimulation_up_to
end FullBridge
