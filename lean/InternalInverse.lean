import RelationComprehension

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem codedRelation_inverse (hp : Pairing s) (hun : Union s)
    (hpow : PowerSet s) (hsep : Separation s) (r : U) :
    ∃ r', ∀ x y, CodedRelation s r' x y ↔ CodedRelation s r y x := by
  obtain ⟨d, hd⟩ := codedRelation_component_bound hun r
  obtain ⟨r', hr'⟩ := bounded_relation_comprehension hp hpow hsep
    (relatedFormula (n := 3) 2 0 1) (cons r Fin.elim0) d
  refine ⟨r', ?_⟩
  intro x y
  have hh : CodedRelation s r' x y ↔
      s x d ∧ s y d ∧ CodedRelation s r y x := by
    have htemp := hr' x y
    rw [eval_relatedFormula] at htemp
    exact htemp
  constructor
  · intro h
    exact ((hh.mp h).2).2
  · intro h
    have hb := hd y x h
    exact hh.mpr ⟨hb.2, hb.1, h⟩

theorem codedBehavior_bisimulation (s : U → U → Prop) :
    Bisimulation s (CodedBehavior s) := by
  intro a b h
  obtain ⟨r, hr, hab⟩ := h
  constructor
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := (hr a b hab).1 x hx
    exact ⟨y, hy, r, hr, hxy⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := (hr a b hab).2 y hy
    exact ⟨x, hx, r, hr, hxy⟩

theorem codedBehavior_symm (hp : Pairing s) (hun : Union s)
    (hpow : PowerSet s) (hsep : Separation s) {a b : U}
    (h : CodedBehavior s a b) : CodedBehavior s b a := by
  obtain ⟨r, hr, hab⟩ := h
  obtain ⟨r', hi⟩ := codedRelation_inverse hp hun hpow hsep r
  refine ⟨r', ?_, (hi b a).mpr hab⟩
  intro x y hxy
  have hyx := (hi x y).mp hxy
  constructor
  · intro z hz
    obtain ⟨w, hw, hwz⟩ := (hr y x hyx).2 z hz
    exact ⟨w, hw, (hi z w).mpr hwz⟩
  · intro w hw
    obtain ⟨z, hz, hwz⟩ := (hr y x hyx).1 w hw
    exact ⟨z, hz, (hi z w).mpr hwz⟩

#print axioms codedBehavior_symm
end FullBridge
