import GraphAxioms

namespace FullBridge
universe u v
variable {U : Type u} {V : Type v}
variable {s : U → U → Prop} {t : V → V → Prop} {q : U → V}

theorem pair_forward (hm : ExactMembers s t q) {p x y : U}
    (hp : IsPair s p x y) : IsPair t (q p) (q x) (q y) := by
  intro z
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := (hm p z).mp hz
    rcases (hp a).mp ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro hz
    rcases hz with rfl | rfl
    · exact (hm p (q x)).mpr ⟨x, (hp x).mpr (Or.inl rfl), rfl⟩
    · exact (hm p (q y)).mpr ⟨y, (hp y).mpr (Or.inr rfl), rfl⟩

theorem orderedPair_forward (hm : ExactMembers s t q) {p x y : U}
    (hp : IsOrderedPair s p x y) : IsOrderedPair t (q p) (q x) (q y) := by
  obtain ⟨a, b, ha, hb, hp⟩ := hp
  exact ⟨q a, q b, pair_forward hm ha, pair_forward hm hb, pair_forward hm hp⟩

theorem codedRelation_forward (hm : ExactMembers s t q) {r x y : U}
    (h : CodedRelation s r x y) : CodedRelation t (q r) (q x) (q y) := by
  obtain ⟨p, hpr, hp⟩ := h
  exact ⟨q p, (hm r (q p)).mpr ⟨p, hpr, rfl⟩, orderedPair_forward hm hp⟩

theorem graphCode_forward (hm : ExactMembers s t q) {a r : U}
    (h : GraphCode s a r) : GraphCode t (q a) (q r) := by
  intro p hp
  obtain ⟨v, hvr, rfl⟩ := (hm r p).mp hp
  obtain ⟨x, y, hxa, hya, hv⟩ := h v hvr
  exact ⟨q x, q y, (hm a (q x)).mpr ⟨x, hxa, rfl⟩,
    (hm a (q y)).mpr ⟨y, hya, rfl⟩, orderedPair_forward hm hv⟩

#print axioms orderedPair_forward
end FullBridge
