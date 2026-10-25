import ParameterCriterion
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem object_outside_set (base : BaseCollection s) (a : U) : ∃ r, ¬s r a := by
  obtain ⟨r, hr⟩ := base.separation 0
    (Formula.impl (.member 0 0) .bottom) Fin.elim0 a
  have hi : ∀ x, s x r ↔ s x a ∧ ¬s x x := hr
  refine ⟨r, ?_⟩
  intro hra
  have hrr : ¬s r r := by
    intro h
    exact ((hi r).mp h).2 h
  exact hrr ((hi r).mpr ⟨hra, hrr⟩)

theorem fresh_orderedPair_tag (base : BaseCollection s) (t : U) :
    ∃ tag, ∀ x p, IsOrderedPair s p tag x → ¬s p t := by
  obtain ⟨d, hd⟩ := codedRelation_component_bound base.union t
  obtain ⟨tag, htag⟩ := object_outside_set base d
  refine ⟨tag, ?_⟩
  intro x p hp hpt
  exact htag (hd tag x ⟨p, hpt, hp⟩).1

theorem tagged_image_exists (base : BaseCollection s) (a tag : U) :
    ∃ b, ∀ p, s p b ↔ ∃ x, s x a ∧ IsOrderedPair s p tag x := by
  have hrep := collection_separation_replacement s base.collection base.separation
  have htotal : ∀ x, s x a → ∃ p,
      Eval s (orderedPairFormula (n := 3) 0 2 1) (cons p (cons x (cons tag Fin.elim0))) ∧
      ∀ z, Eval s (orderedPairFormula (n := 3) 0 2 1) (cons z (cons x (cons tag Fin.elim0))) → z = p := by
    intro x _
    obtain ⟨p, hp⟩ := orderedPair_exists base.pairing tag x
    refine ⟨p, (eval_orderedPairFormula s 0 2 1 _).mpr hp, ?_⟩
    intro z hz
    exact orderedPair_unique base.extensional ((eval_orderedPairFormula s 0 2 1 _).mp hz) hp
  obtain ⟨b, hb⟩ := hrep 1 (orderedPairFormula 0 2 1) (cons tag Fin.elim0) a htotal
  refine ⟨b, ?_⟩
  intro p
  have h := hb p
  simp only [eval_orderedPairFormula] at h
  exact h

def tagFunctionFormula : Formula 4 :=
  .conj (.member 1 2) (orderedPairFormula 0 3 1)

theorem eval_tagFunctionFormula (y x a tag : U) :
    Eval s tagFunctionFormula (cons y (cons x (cons a (cons tag Fin.elim0)))) ↔
      s x a ∧ IsOrderedPair s y tag x := by
  simp only [tagFunctionFormula, Eval, eval_orderedPairFormula]
  rfl

theorem fresh_parameter_copy (base : BaseCollection s) (a t : U) :
    ∃ b f, FunctionCode s a f ∧ InjectiveCode s f ∧ RangeCode s a f b ∧
      ∀ z, s z b → ¬s z t := by
  obtain ⟨tag, htag⟩ := fresh_orderedPair_tag base t
  obtain ⟨b, hb⟩ := tagged_image_exists base a tag
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union a b
  obtain ⟨f, hfmem⟩ := relation_comprehension_members base tagFunctionFormula
    (cons a (cons tag Fin.elim0)) d
  have hi : ∀ x y, CodedRelation s f x y ↔ s x a ∧ IsOrderedPair s y tag x := by
    intro x y
    constructor
    · rintro ⟨p, hp, hpxy⟩
      obtain ⟨x', y', _, _, hp', hev⟩ := (hfmem p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxy hp'
      exact (eval_tagFunctionFormula _ _ a tag).mp hev
    · rintro ⟨hx, hy⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x y
      exact ⟨p, (hfmem p).mpr ⟨x, y, (hd x).mpr (Or.inl hx),
        (hd y).mpr (Or.inr ((hb y).mpr ⟨x, hx, hy⟩)), hp,
        (eval_tagFunctionFormula y x a tag).mpr ⟨hx, hy⟩⟩, hp⟩
  refine ⟨b, f, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, y, _, _, hpxy, hev⟩ := (hfmem p).mp hp
    exact ⟨x, y, ((eval_tagFunctionFormula y x a tag).mp hev).1, hpxy⟩
  · intro x hx
    obtain ⟨y, hy⟩ := orderedPair_exists base.pairing tag x
    refine ⟨y, (hi x y).mpr ⟨hx, hy⟩, ?_⟩
    intro z hz
    exact orderedPair_unique base.extensional ((hi x z).mp hz).2 hy
  · intro x y z hxz hyz
    exact (orderedPair_injective ((hi x z).mp hxz).2 ((hi y z).mp hyz).2).2
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := (hb y).mp hy
      exact ⟨x, hx, (hi x y).mpr ⟨hx, hxy⟩⟩
    · rintro ⟨x, hx, hxy⟩
      exact (hb y).mpr ⟨x, hx, ((hi x y).mp hxy).2⟩
  · intro z hz
    obtain ⟨x, _, hzx⟩ := (hb z).mp hz
    exact htag x z hzx

#print axioms fresh_parameter_copy
end FullBridge
