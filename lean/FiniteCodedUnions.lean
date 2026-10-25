import BafaCoherentRealization
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

/-- An externally finite family has an actual source union, without an
    assumed source code for its index type or family. -/
theorem finite_indexed_union (base : BaseCollection s) {I : Type v}
    (is : List I) (f : I → U) :
    ∃ b, ∀ x, s x b ↔ ∃ i, i ∈ is ∧ s x (f i) := by
  induction is with
  | nil =>
    obtain ⟨b, hb⟩ := base.empty
    exact ⟨b, fun x => ⟨fun h => False.elim (hb x h), fun ⟨i, hi, _⟩ => False.elim (by simp at hi)⟩⟩
  | cons i is ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨c, hc⟩ := binary_union_exists base.pairing base.union (f i) b
    refine ⟨c, fun x => ?_⟩
    rw [hc, hb]
    constructor
    · rintro (hi | ⟨j, hj, hxj⟩)
      · exact ⟨i, by simp, hi⟩
      · exact ⟨j, by simp [hj], hxj⟩
    · rintro ⟨j, hj, hxj⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact Or.inl hxj
      · exact Or.inr ⟨j, hj, hxj⟩

theorem finite_indexed_relation_union (base : BaseCollection s) {I : Type v}
    (is : List I) (f : I → U) :
    ∃ r, (∀ z, s z r ↔ ∃ i, i ∈ is ∧ s z (f i)) ∧
      ∀ x y, CodedRelation s r x y ↔ ∃ i, i ∈ is ∧ CodedRelation s (f i) x y := by
  obtain ⟨r, hr⟩ := finite_indexed_union base is f
  refine ⟨r, hr, fun x y => ?_⟩
  constructor
  · rintro ⟨z, hz, hxy⟩
    obtain ⟨i, hi, hzi⟩ := (hr z).mp hz
    exact ⟨i, hi, z, hzi, hxy⟩
  · rintro ⟨i, hi, z, hz, hxy⟩
    exact ⟨z, (hr z).mpr ⟨i, hi, hz⟩, hxy⟩

#print axioms finite_indexed_relation_union
end FullBridge
