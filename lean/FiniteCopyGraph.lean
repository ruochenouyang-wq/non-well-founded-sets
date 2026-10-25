import FiniteCopies
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

theorem copied_membership_agrees_on_old {t A p B k E : U}
    (ht : TransitiveCode s t) (hp : MembershipIsoCode s t t p)
    (hk : CopyCode s t A p B k)
    (hE : ∀ X Y, CodedRelation s E X Y ↔
      ∃ x y, CodedRelation s k x X ∧ CodedRelation s k y Y ∧ s y x) :
    ∀ X, s X t → ∀ Y, CodedRelation s E X Y ↔ s Y X := by
  intro X hX Y
  obtain ⟨x, hx, hxX⟩ := (hp.2.2.1 X).mp hX
  have hpk := hk.2.2.2.2
  constructor
  · intro hXY
    obtain ⟨u, v, huX, hvY, hvu⟩ := (hE X Y).mp hXY
    have hux := hk.2.1 u x X huX (hpk x X hxX)
    have hvx : s v x := hux ▸ hvu
    obtain ⟨V, hvV, _⟩ := hp.1.2 v (ht x hx v hvx)
    have hVY := coded_function_value_unique hk.1 (hpk v V hvV) hvY
    exact hVY ▸ (hp.2.2.2 x v X V hxX hvV).mp hvx
  · intro hYX
    obtain ⟨y, _, hyY⟩ := (hp.2.2.1 Y).mp (ht X hX Y hYX)
    exact (hE X Y).mpr ⟨x, y, hpk x X hxX, hpk y Y hyY,
      (hp.2.2.2 x y X Y hxX hyY).mpr hYX⟩

/-- Construct the actual finite multi-copy graph. Its rows agree with the
    transported membership graph on each copy, and each copy is graph-closed.
    A multiplication action on this graph is a subsequent obligation. -/
theorem finite_membership_amalgam (base : BaseCollection s) {I : Type v}
    {t A : U} (ht : TransitiveCode s t) (hA : TransitiveCode s A) (htA : Subset s t A)
    (one : I) (act : I → U) (hp : ∀ i, MembershipIsoCode s t t (act i))
    (hOne : ∀ x y, CodedRelation s (act one) x y → x = y)
    (is : List I) (hAll : ∀ i, i ∈ is) :
    ∃ ranges codes : I → U, ∃ S e,
      ranges one = A ∧
      (∀ x y, CodedRelation s (codes one) x y ↔ s x A ∧ y = x) ∧
      (∀ i, CopyCode s t A (act i) (ranges i) (codes i)) ∧
      (∀ i j, i ≠ j → ∀ x, s x (ranges i) ∧ s x (ranges j) ↔ s x t) ∧
      (∀ X, s X S ↔ ∃ i, s X (ranges i)) ∧ GraphCode s S e ∧
      EndExtensionCode s S e A ∧ (∀ i, GraphClosedCode s S e (ranges i)) ∧
      (∀ i x y X Y, CodedRelation s (codes i) x X → CodedRelation s (codes i) y Y →
        (CodedRelation s e X Y ↔ s y x)) := by
  classical
  obtain ⟨ranges, codes, hIdRange, hId, hc, hInt⟩ := finite_copy_family base hA htA one act hp hOne is hAll
  have hExists : ∀ i, ∃ E, GraphCode s (ranges i) E ∧
      ∀ X Y, CodedRelation s E X Y ↔
        ∃ x y, CodedRelation s (codes i) x X ∧ CodedRelation s (codes i) y Y ∧ s y x :=
    fun i => transported_membership_graph base (hc i).1 (hc i).2.2.1
  let edges : I → U := fun i => Classical.choose (hExists i)
  have he : ∀ i, GraphCode s (ranges i) (edges i) ∧
      ∀ X Y, CodedRelation s (edges i) X Y ↔
        ∃ x y, CodedRelation s (codes i) x X ∧ CodedRelation s (codes i) y Y ∧ s y x :=
    fun i => Classical.choose_spec (hExists i)
  obtain ⟨S, hS⟩ := finite_indexed_union base is ranges
  have hS' : ∀ X, s X S ↔ ∃ i, s X (ranges i) := by
    intro X
    exact (hS X).trans ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, hAll i, h⟩⟩
  obtain ⟨e, hemem, her⟩ := finite_indexed_relation_union base is edges
  have her' : ∀ X Y, CodedRelation s e X Y ↔ ∃ i, CodedRelation s (edges i) X Y := by
    intro X Y
    exact (her X Y).trans ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, hAll i, h⟩⟩
  have hG : GraphCode s S e := by
    intro z hz
    obtain ⟨i, _, hzi⟩ := (hemem z).mp hz
    obtain ⟨X, Y, hX, hY, hXY⟩ := (he i).1 z hzi
    exact ⟨X, Y, (hS' X).mpr ⟨i, hX⟩, (hS' Y).mpr ⟨i, hY⟩, hXY⟩
  have hOld := fun i => copied_membership_agrees_on_old ht (hp i) (hc i) (he i).2
  have hRow : ∀ i X, s X (ranges i) → ∀ Y,
      CodedRelation s e X Y ↔ CodedRelation s (edges i) X Y := by
    intro i X hX Y
    constructor
    · intro hXY
      obtain ⟨j, hj⟩ := (her' X Y).mp hXY
      by_cases hij : i = j
      · exact hij.symm ▸ hj
      · have hXt := (hInt i j hij X).mp ⟨hX, (graphCode_endpoints (he j).1 hj).1⟩
        exact (hOld i X hXt Y).mpr ((hOld j X hXt Y).mp hj)
    · exact fun h => (her' X Y).mpr ⟨i, h⟩
  have hEnd : EndExtensionCode s S e A := by
    refine ⟨fun X hX => (hS' X).mpr ⟨one, hIdRange.symm ▸ hX⟩, ?_⟩
    intro X hX Y
    rw [hRow one X (hIdRange.symm ▸ hX) Y, (he one).2 X Y]
    constructor
    · rintro ⟨x, y, hxX, hyY, hyx⟩
      have hXx := ((hId x X).mp hxX).2
      have hYy := ((hId y Y).mp hyY).2
      exact hXx.symm ▸ hYy.symm ▸ hyx
    · intro hYX
      exact ⟨X, Y, (hId X X).mpr ⟨hX, rfl⟩,
        (hId Y Y).mpr ⟨hA X hX Y hYX, rfl⟩, hYX⟩
  refine ⟨ranges, codes, S, e, hIdRange, hId, hc, hInt, hS', hG, hEnd, ?_, ?_⟩
  · intro i
    exact ⟨fun X hX => (hS' X).mpr ⟨i, hX⟩,
      fun X hX Y hXY => (graphCode_endpoints (he i).1 ((hRow i X hX Y).mp hXY)).2⟩
  · intro i x y X Y hxX hyY
    have hX := ((hc i).2.2.1 X).mpr ⟨x, coded_function_domain (hc i).1 hxX, hxX⟩
    exact (hRow i X hX Y).trans (transported_membership_edge_iff (hc i).2.1 (he i).2 hxX hyY)

#print axioms finite_membership_amalgam
end FullBridge
