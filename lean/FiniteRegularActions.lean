import FiniteQuineLabels
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

theorem finite_group_left_cancel {I : Type v} (G : FiniteGroupData I) {i k l : I}
    (h : G.mul i k = G.mul i l) : k = l := by
  have he := congrArg (G.mul (G.inv i)) h
  simpa only [finite_group_left_inverse] using he

/-- Finite singleton-relation unions, then normalization, construct the actual
    source codes of the regular permutation action on distinct labels. -/
theorem finite_regular_action_codes (base : BaseCollection s) {I : Type v} (G : FiniteGroupData I)
    {a : U} (q : I → U) (hmem : ∀ x, s x a ↔ ∃ i, x = q i) :
    ∃ act : I → U, ∀ i, GraphCode s a (act i) ∧
      ∀ X Y, CodedRelation s (act i) X Y ↔ ∃ k, X = q k ∧ Y = q (G.mul i k) := by
  classical
  have hSingle := fun i k => codedRelation_singleton base.pairing (q k) (q (G.mul i k))
  let single : I → I → U := fun i k => Classical.choose (hSingle i k)
  have hs := fun i k => Classical.choose_spec (hSingle i k)
  have hUnion := fun i => finite_indexed_relation_union base G.indices (single i)
  let unionCode : I → U := fun i => Classical.choose (hUnion i)
  have hu := fun i => Classical.choose_spec (hUnion i)
  have hNorm := fun i => normalized_relation_comprehension base (relatedFormula 2 1 0 : Formula 3)
    (cons (unionCode i) Fin.elim0) a
  let act : I → U := fun i => Classical.choose (hNorm i)
  have hn := fun i => Classical.choose_spec (hNorm i)
  refine ⟨act, fun i => ⟨(hn i).1, fun X Y => ?_⟩⟩
  have hN : CodedRelation s (act i) X Y ↔ s X a ∧ s Y a ∧ CodedRelation s (unionCode i) X Y := by
    refine ((hn i).2 X Y).trans (and_congr Iff.rfl (and_congr Iff.rfl ?_))
    exact eval_relatedFormula s 2 1 0 _
  rw [hN, (hu i).2 X Y]
  constructor
  · rintro ⟨_, _, k, _, hk⟩
    exact ⟨k, (hs i k X Y).mp hk⟩
  · rintro ⟨k, rfl, rfl⟩
    exact ⟨(hmem (q k)).mpr ⟨k, rfl⟩, (hmem (q (G.mul i k))).mpr ⟨G.mul i k, rfl⟩,
      k, G.complete k, (hs i k _ _).mpr ⟨rfl, rfl⟩⟩

theorem finite_quine_regular_action (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (G : FiniteGroupData I) :
    ∃ P : TransitiveGroupAction s G, ∃ q : I → U,
      (∀ i, SelfSingleton s (q i)) ∧ (∀ i j, q i = q j → i = j) ∧
      (∀ x, s x P.domain ↔ ∃ k, x = q k) ∧
      (∀ i X Y, CodedRelation s (P.code i) X Y ↔ ∃ k, X = q k ∧ Y = q (G.mul i k)) := by
  obtain ⟨a, q, ha, hq, hqi, hmem⟩ := finite_distinct_quine_set base hB G.indices G.complete
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
  exact ⟨⟨a, act, ha, hIso, hOne, hMul⟩, q, hq, hqi, hmem, hr⟩

/-- Every specified external finite group has a faithful global action in a
    BAFA model with a supplied external countable enumeration. -/
theorem countable_bafa_faithful_finite_group (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (G : FiniteGroupData I) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : I → U → U, ∃ q : I → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ x, J G.one x = x) ∧ (∀ i j x, J (G.mul i j) x = J i (J j x)) ∧
      (∀ i k, J i (q k) = q (G.mul i k)) ∧ (∀ i, SelfSingleton s (q i)) ∧
      (∀ i j, q i = q j → i = j) ∧ (∀ i j, (∀ x, J i x = J j x) → i = j) ∧
      (∀ i x, internalCode base (J i x) = internalCode base x) ∧
      (∀ i a, ∃ f, FunctionCode s a f ∧ ∀ x y, CodedRelation s f x y ↔ s x a ∧ J i x = y) := by
  obtain ⟨P, q, hq, hqi, _, hreg⟩ := finite_quine_regular_action base hB G
  obtain ⟨J, hJ, hOne, hMul, hExt, hQ, hLocal⟩ := countable_bafa_group_extension base hB G P enum henum
  have hOrbit : ∀ i k, J i (q k) = q (G.mul i k) :=
    fun i k => hExt i _ _ ((hreg i _ _).mpr ⟨k, rfl, rfl⟩)
  refine ⟨J, q, hJ, hOne, hMul, hOrbit, hq, hqi, ?_, hQ, hLocal⟩
  intro i j hij
  apply hqi i j
  have hi : J i (q G.one) = q i := by simpa only [G.mul_one] using hOrbit i G.one
  have hj : J j (q G.one) = q j := by simpa only [G.mul_one] using hOrbit j G.one
  exact hi.symm.trans ((hij (q G.one)).trans hj)

#print axioms finite_quine_regular_action
#print axioms countable_bafa_faithful_finite_group
end FullBridge
