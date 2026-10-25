import CountableBafaGroupActions
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

theorem finite_partial_quine_labels (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (is : List I) :
    ∃ q : I → U, ∃ b, (∀ i, i ∈ is → SelfSingleton s (q i) ∧ s (q i) b) ∧
      (∀ i j, i ∈ is → j ∈ is → q i = q j → i = j) := by
  classical
  induction is with
  | nil =>
    obtain ⟨e, _⟩ := base.empty
    exact ⟨fun _ => e, e, fun i hi => False.elim (by simp at hi),
      fun i _ hi => False.elim (by simp at hi)⟩
  | cons i is ih =>
    obtain ⟨q, b, hq, hinj⟩ := ih
    by_cases hi : i ∈ is
    · have hback : ∀ j, j ∈ i :: is → j ∈ is := by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi
        · exact hj
      exact ⟨q, b, fun j hj => hq j (hback j hj),
        fun j k hj hk => hinj j k (hback j hj) (hback k hk)⟩
    · obtain ⟨u, hu, hub⟩ := bafa_selfSingleton_outside_set base hB b
      obtain ⟨B, hBmem⟩ := binary_union_exists base.pairing base.union b u
      let Q : I → U := fun j => if j = i then u else q j
      have hback : ∀ j, j ∈ i :: is → j ≠ i → j ∈ is :=
        fun j hj hji => (List.mem_cons.mp hj).resolve_left hji
      refine ⟨Q, B, ?_, ?_⟩
      · intro j hj
        by_cases hji : j = i
        · subst j
          exact ⟨by simpa [Q] using hu, by simpa [Q] using (hBmem u).mpr (Or.inr ((hu u).mpr rfl))⟩
        · have h := hq j (hback j hj hji)
          exact ⟨by simpa [Q, hji] using h.1, by simpa [Q, hji] using (hBmem (q j)).mpr (Or.inl h.2)⟩
      · intro j k hj hk heq
        by_cases hji : j = i
        · subst j
          by_cases hki : k = i
          · exact hki.symm
          · have he : u = q k := by simpa [Q, hki] using heq
            exact False.elim (hub (he.symm ▸ (hq k (hback k hk hki)).2))
        · by_cases hki : k = i
          · subst k
            have he : q j = u := by simpa [Q, hji] using heq
            exact False.elim (hub (he ▸ (hq j (hback j hj hji)).2))
          · exact hinj j k (hback j hj hji) (hback k hk hki) (by simpa [Q, hji, hki] using heq)

/-- An actual transitive source set consisting of distinct quines indexed by
    a specified external finite type. No infinite indexed family is claimed. -/
theorem finite_distinct_quine_set (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (is : List I) (hAll : ∀ i, i ∈ is) :
    ∃ a, ∃ q : I → U, TransitiveCode s a ∧ (∀ i, SelfSingleton s (q i)) ∧
      (∀ i j, q i = q j → i = j) ∧ (∀ x, s x a ↔ ∃ i, x = q i) := by
  obtain ⟨q, _, hq, hi⟩ := finite_partial_quine_labels base hB is
  obtain ⟨a, ha⟩ := finite_indexed_union base is q
  have hmem : ∀ x, s x a ↔ ∃ i, x = q i := by
    intro x
    exact (ha x).trans ⟨fun ⟨i, hit, hx⟩ => ⟨i, ((hq i hit).1 x).mp hx⟩,
      fun ⟨i, hx⟩ => ⟨i, hAll i, ((hq i (hAll i)).1 x).mpr hx⟩⟩
  refine ⟨a, q, ?_, fun i => (hq i (hAll i)).1, fun i j => hi i j (hAll i) (hAll j), hmem⟩
  intro x hx y hyx
  obtain ⟨i, rfl⟩ := (hmem x).mp hx
  exact (hmem y).mpr ⟨i, ((hq i (hAll i)).1 y).mp hyx⟩

#print axioms finite_distinct_quine_set
end FullBridge
