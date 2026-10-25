import InternalSyntax

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem pair_unique (he : Extensional s) {p q x y : U}
    (hp : IsPair s p x y) (hq : IsPair s q x y) : p = q := by
  apply he p q
  intro z
  exact (hp z).trans (hq z).symm

theorem orderedPair_exists (hp : Pairing s) (x y : U) : ∃ p, IsOrderedPair s p x y := by
  obtain ⟨a, ha⟩ := hp x x
  obtain ⟨b, hb⟩ := hp x y
  obtain ⟨p, hpair⟩ := hp a b
  exact ⟨p, a, b, ha, hb, hpair⟩

theorem orderedPair_unique (he : Extensional s) {p q x y : U}
    (hp : IsOrderedPair s p x y) (hq : IsOrderedPair s q x y) : p = q := by
  obtain ⟨a, b, ha, hb, hp⟩ := hp
  obtain ⟨c, d, hc, hd, hq⟩ := hq
  have hac := pair_unique he ha hc
  have hbd := pair_unique he hb hd
  subst c
  subst d
  exact pair_unique he hp hq

theorem orderedPair_first {p x y z : U} (hp : IsOrderedPair s p x y) :
    (∀ c, s c p → s z c) ↔ z = x := by
  obtain ⟨a, b, ha, hb, hp⟩ := hp
  constructor
  · intro h
    have hz := (ha z).mp (h a ((hp a).mpr (Or.inl rfl)))
    exact hz.elim id id
  · intro hz
    subst z
    intro c hc
    rcases (hp c).mp hc with rfl | rfl
    · exact (ha x).mpr (Or.inl rfl)
    · exact (hb x).mpr (Or.inl rfl)

theorem orderedPair_union {p x y z : U} (hp : IsOrderedPair s p x y) :
    (∃ c, s c p ∧ s z c) ↔ z = x ∨ z = y := by
  obtain ⟨a, b, ha, hb, hp⟩ := hp
  constructor
  · rintro ⟨c, hc, hz⟩
    rcases (hp c).mp hc with rfl | rfl
    · exact Or.inl (((ha z).mp hz).elim id id)
    · exact (hb z).mp hz
  · intro hz
    exact ⟨b, (hp b).mpr (Or.inr rfl), (hb z).mpr hz⟩

theorem orderedPair_injective {p x y x' y' : U}
    (hp : IsOrderedPair s p x y) (hq : IsOrderedPair s p x' y') : x = x' ∧ y = y' := by
  have hxx : x = x' := (orderedPair_first hq).mp ((orderedPair_first hp).mpr rfl)
  subst x'
  have hu : ∀ z, (z = x ∨ z = y) ↔ (z = x ∨ z = y') := by
    intro z
    exact (orderedPair_union hp).symm.trans (orderedPair_union hq)
  have hyy := (hu y).mp (Or.inr rfl)
  have hy'y := (hu y').mpr (Or.inr rfl)
  refine ⟨rfl, ?_⟩
  rcases hyy with hyx | hyy'
  · rcases hy'y with hy'x | hy'y
    · exact hyx.trans hy'x.symm
    · exact hy'y.symm
  · exact hyy'

/- Components of a coded relation are bounded by two unions of its code. -/
theorem codedRelation_component_bound (hun : Union s) (r : U) :
    ∃ d, ∀ x y, CodedRelation s r x y → s x d ∧ s y d := by
  obtain ⟨u, hu⟩ := hun r
  obtain ⟨d, hd⟩ := hun u
  refine ⟨d, ?_⟩
  intro x y h
  obtain ⟨p, hpr, hp⟩ := h
  constructor
  · obtain ⟨a, hap, hxa⟩ := (orderedPair_union hp).mpr (Or.inl rfl)
    exact (hd x).mpr ⟨a, (hu a).mpr ⟨p, hpr, hap⟩, hxa⟩
  · obtain ⟨b, hbp, hyb⟩ := (orderedPair_union hp).mpr (Or.inr rfl)
    exact (hd y).mpr ⟨b, (hu b).mpr ⟨p, hpr, hbp⟩, hyb⟩

#print axioms orderedPair_injective
end FullBridge
