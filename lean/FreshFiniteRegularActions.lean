import GrowingGroupLimits
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

theorem finite_partial_quine_labels_outside (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (L : U) (is : List I) :
    ∃ q : I → U, ∃ b, Subset s L b ∧ (∀ i, i ∈ is → SelfSingleton s (q i) ∧ s (q i) b ∧ ¬ s (q i) L) ∧
      (∀ i j, i ∈ is → j ∈ is → q i = q j → i = j) := by
  classical
  induction is with
  | nil =>
    obtain ⟨e, _⟩ := base.empty
    exact ⟨fun _ => e, L, fun _ hx => hx, fun i hi => False.elim (by simp at hi),
      fun i _ hi => False.elim (by simp at hi)⟩
  | cons i is ih =>
    obtain ⟨q, b, hLb, hq, hinj⟩ := ih
    by_cases hi : i ∈ is
    · have hback : ∀ j, j ∈ i :: is → j ∈ is := by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi
        · exact hj
      exact ⟨q, b, hLb, fun j hj => hq j (hback j hj),
        fun j k hj hk => hinj j k (hback j hj) (hback k hk)⟩
    · obtain ⟨u, hu, hub⟩ := bafa_selfSingleton_outside_set base hB b
      obtain ⟨B, hBmem⟩ := binary_union_exists base.pairing base.union b u
      let Q : I → U := fun j => if j = i then u else q j
      have hback : ∀ j, j ∈ i :: is → j ≠ i → j ∈ is :=
        fun j hj hji => (List.mem_cons.mp hj).resolve_left hji
      refine ⟨Q, B, fun x hx => (hBmem x).mpr (Or.inl (hLb x hx)), ?_, ?_⟩
      · intro j hj
        by_cases hji : j = i
        · subst j
          exact ⟨by simpa [Q] using hu, by simpa [Q] using (hBmem u).mpr (Or.inr ((hu u).mpr rfl)), by simpa [Q] using (fun h => hub (hLb u h))⟩
        · have h := hq j (hback j hj hji)
          exact ⟨by simpa [Q, hji] using h.1, by simpa [Q, hji] using (hBmem (q j)).mpr (Or.inl h.2.1), by simpa [Q, hji] using h.2.2⟩
      · intro j k hj hk heq
        by_cases hji : j = i
        · subst j
          by_cases hki : k = i
          · exact hki.symm
          · have he : u = q k := by simpa [Q, hki] using heq
            exact False.elim (hub (he.symm ▸ (hq k (hback k hk hki)).2.1))
        · by_cases hki : k = i
          · subst k
            have he : q j = u := by simpa [Q, hji] using heq
            exact False.elim (hub (he ▸ (hq j (hback j hj hji)).2.1))
          · exact hinj j k (hback j hj hji) (hback k hk hki) (by simpa [Q, hji, hki] using heq)


theorem finite_distinct_quine_set_outside (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (L : U) (is : List I) (hAll : ∀ i, i ∈ is) :
    ∃ a, ∃ q : I → U, TransitiveCode s a ∧ (∀ i, SelfSingleton s (q i)) ∧
      (∀ i j, q i = q j → i = j) ∧ (∀ x, s x a ↔ ∃ i, x = q i) ∧
      (∀ x, s x a → ¬ s x L) := by
  obtain ⟨q, _, _, hq, hi⟩ := finite_partial_quine_labels_outside base hB L is
  obtain ⟨a, ha⟩ := finite_indexed_union base is q
  have hmem : ∀ x, s x a ↔ ∃ i, x = q i := by
    intro x
    exact (ha x).trans ⟨fun ⟨i, hit, hx⟩ => ⟨i, ((hq i hit).1 x).mp hx⟩,
      fun ⟨i, hx⟩ => ⟨i, hAll i, ((hq i (hAll i)).1 x).mpr hx⟩⟩
  refine ⟨a, q, ?_, fun i => (hq i (hAll i)).1, fun i j => hi i j (hAll i) (hAll j), hmem, ?_⟩
  · intro x hx y hyx
    obtain ⟨i, rfl⟩ := (hmem x).mp hx
    exact (hmem y).mpr ⟨i, ((hq i (hAll i)).1 y).mp hyx⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := (hmem x).mp hx
    exact (hq i (hAll i)).2.2
theorem finite_quine_regular_action_outside (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (G : FiniteGroupData I) (L : U) :
    ∃ P : TransitiveGroupAction s G, ∃ q : I → U,
      (∀ i, SelfSingleton s (q i)) ∧ (∀ i j, q i = q j → i = j) ∧
      (∀ x, s x P.domain ↔ ∃ k, x = q k) ∧
      (∀ i X Y, CodedRelation s (P.code i) X Y ↔ ∃ k, X = q k ∧ Y = q (G.mul i k)) ∧ (∀ x, s x P.domain → ¬ s x L) := by
  obtain ⟨a, q, ha, hq, hqi, hmem, hDisj⟩ := finite_distinct_quine_set_outside base hB L G.indices G.complete
  obtain ⟨act, hact⟩ := finite_regular_action_codes base G q hmem
  have hr := fun i => (hact i).2
  have hf : ∀ i, FunctionCode s a (act i) := by
    intro i
    constructor
    · intro z hz
      obtain ⟨X, Y, hX, _, hXY⟩ := (hact i).1 z hz
      exact ⟨X, Y, hX, hXY⟩
    · intro X hX
      obtain ⟨k, rfl⟩ := (hmem X).mp hX
      refine ⟨q (G.mul i k), (hr i _ _).mpr ⟨k, rfl, rfl⟩, ?_⟩
      intro Z hXZ
      obtain ⟨l, hkl, hZ⟩ := (hr i _ _).mp hXZ
      exact hZ.trans (congrArg (fun j => q (G.mul i j)) (hqi k l hkl).symm)
  have hInj : ∀ i, InjectiveCode s (act i) := by
    intro i X Y Z hXZ hYZ
    obtain ⟨k, rfl, hZk⟩ := (hr i X Z).mp hXZ
    obtain ⟨l, rfl, hZl⟩ := (hr i Y Z).mp hYZ
    exact congrArg q (finite_group_left_cancel G (hqi _ _ (hZk.symm.trans hZl)))
  have hRange : ∀ i, RangeCode s a (act i) a := by
    intro i Y
    constructor
    · intro hY
      obtain ⟨k, rfl⟩ := (hmem Y).mp hY
      exact ⟨q (G.mul (G.inv i) k), (hmem _).mpr ⟨_, rfl⟩,
        (hr i _ _).mpr ⟨G.mul (G.inv i) k, rfl, by rw [finite_group_right_inverse]⟩⟩
    · rintro ⟨X, _, hXY⟩
      obtain ⟨k, _, hY⟩ := (hr i X Y).mp hXY
      exact (hmem Y).mpr ⟨G.mul i k, hY⟩
  have hIso : ∀ i, MembershipIsoCode s a a (act i) := by
    intro i
    refine ⟨hf i, hInj i, hRange i, ?_⟩
    intro x y X Y hxX hyY
    obtain ⟨k, rfl, rfl⟩ := (hr i x X).mp hxX
    obtain ⟨l, rfl, rfl⟩ := (hr i y Y).mp hyY
    rw [hq k (q l), hq (G.mul i k) (q (G.mul i l))]
    exact ⟨fun h => congrArg (fun j => q (G.mul i j)) (hqi l k h),
      fun h => congrArg q (finite_group_left_cancel G (hqi _ _ h))⟩
  have hOne : ∀ x y, CodedRelation s (act G.one) x y → x = y := by
    intro x y hxy
    obtain ⟨k, rfl, rfl⟩ := (hr G.one x y).mp hxy
    rw [G.one_mul]
  have hMul : ∀ i j x z, CodedRelation s (act (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (act j) x y ∧ CodedRelation s (act i) y z := by
    intro i j x z
    constructor
    · intro hxz
      obtain ⟨k, rfl, rfl⟩ := (hr (G.mul i j) x z).mp hxz
      exact ⟨q (G.mul j k), (hr j _ _).mpr ⟨k, rfl, rfl⟩,
        (hr i _ _).mpr ⟨G.mul j k, rfl, by rw [G.assoc]⟩⟩
    · rintro ⟨y, hxy, hyz⟩
      obtain ⟨k, rfl, rfl⟩ := (hr j x y).mp hxy
      obtain ⟨l, hkl, rfl⟩ := (hr i _ z).mp hyz
      have hl := (hqi _ _ hkl).symm
      exact (hr (G.mul i j) _ _).mpr ⟨k, rfl, by rw [hl, G.assoc]⟩
  exact ⟨⟨a, act, ha, hIso, hOne, hMul⟩, q, hq, hqi, hmem, hr, hDisj⟩


#print axioms finite_quine_regular_action_outside
end FullBridge
