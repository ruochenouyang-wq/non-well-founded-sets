import JointMaskCopyFamilies
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem coded_family_union (base : BaseCollection s) (G R : U) :
    ∃ S, ∀ X, s X S ↔ ∃ i b, s i G ∧ CodedRelation s R i b ∧ s X b := by
  obtain ⟨r, hr⟩ := coded_image_set_exists base R G
  obtain ⟨S, hS⟩ := base.union r
  refine ⟨S, fun X => ?_⟩
  constructor
  · intro hX
    obtain ⟨b, hb, hXb⟩ := (hS X).mp hX
    obtain ⟨i, hi, hib⟩ := (hr b).mp hb
    exact ⟨i, b, hi, hib, hXb⟩
  · rintro ⟨i, b, hi, hib, hXb⟩
    exact (hS X).mpr ⟨b, (hr b).mpr ⟨i, hi, hib⟩, hXb⟩

/-- Free variables [target,source,index-domain,copy-family]. -/
def internalCopyEdgeFormula : Formula 4 :=
  .ex (.ex (.ex (.ex (.conj (.member 3 6) (.conj (relatedFormula 7 3 2)
    (.conj (relatedFormula 2 1 5) (.conj (relatedFormula 2 0 4) (.member 0 1))))))))

theorem eval_internalCopyEdgeFormula (X Y G K : U) :
    Eval s internalCopyEdgeFormula (cons Y (cons X (cons G (cons K Fin.elim0)))) ↔
      ∃ i k x y, s i G ∧ CodedRelation s K i k ∧ CodedRelation s k x X ∧
        CodedRelation s k y Y ∧ s y x := by
  simp only [internalCopyEdgeFormula, Eval, eval_relatedFormula]
  rfl

structure InternalMembershipAmalgam (s : U → U → Prop) (G t A : U) (F : InternalIsoFamily s G t) where
  copies : InternalCopyFamily s G t A F
  domain : U
  edges : U
  domainMembers : ∀ X, s X domain ↔ ∃ i b, s i G ∧ CodedRelation s copies.ranges i b ∧ s X b
  graph : GraphCode s domain edges
  endExtension : EndExtensionCode s domain edges A
  closed : ∀ i b, CodedRelation s copies.ranges i b → GraphClosedCode s domain edges b
  transported : ∀ i k, CodedRelation s copies.codes i k → ∀ x y X Y,
    CodedRelation s k x X → CodedRelation s k y Y → (CodedRelation s edges X Y ↔ s y x)

/-- The whole internally indexed copy family has an actual source edge
    graph. Each copy is graph-closed and the original A is an end extension. -/
theorem internal_membership_amalgam (base : BaseCollection s) {G t A : U}
    (F : InternalIsoFamily s G t) (ht : TransitiveCode s t) (hA : TransitiveCode s A)
    (htA : Subset s t A) : Nonempty (InternalMembershipAmalgam s G t A F) := by
  classical
  obtain ⟨C⟩ := internal_copy_family_exists base F htA
  let I := {i : U // s i G}
  let ranges : I → U := fun i => Classical.choose (C.rangesFunction.2 i.val i.property)
  let codes : I → U := fun i => Classical.choose (C.codesFunction.2 i.val i.property)
  let act : I → U := fun i => Classical.choose (F.function.2 i.val i.property)
  have hrange : ∀ i : I, CodedRelation s C.ranges i.val (ranges i) :=
    fun i => (Classical.choose_spec (C.rangesFunction.2 i.val i.property)).1
  have hcode : ∀ i : I, CodedRelation s C.codes i.val (codes i) :=
    fun i => (Classical.choose_spec (C.codesFunction.2 i.val i.property)).1
  have hact : ∀ i : I, CodedRelation s F.code i.val (act i) :=
    fun i => (Classical.choose_spec (F.function.2 i.val i.property)).1
  have hp : ∀ i, MembershipIsoCode s t t (act i) := fun i => F.iso i.val (act i) (hact i)
  have hc : ∀ i, CopyCode s t A (act i) (ranges i) (codes i) :=
    fun i => C.copy i.val i.property (ranges i) (codes i) (hrange i) (hcode i) (act i) (hact i)
  have hInt : ∀ i j : I, i ≠ j → ∀ X, s X (ranges i) ∧ s X (ranges j) ↔ s X t := by
    intro i j hij X
    exact C.overlaps i.val j.val (ranges i) (ranges j) (fun he => hij (Subtype.ext he)) (hrange i) (hrange j) X
  let one : I := ⟨F.one, F.one_mem⟩
  have hIdRange : ranges one = A := C.identityRange _ (hrange one)
  have hId : ∀ x y, CodedRelation s (codes one) x y ↔ s x A ∧ y = x := C.identityMap _ (hcode one)
  obtain ⟨S, hS⟩ := coded_family_union base G C.ranges
  have hS' : ∀ X, s X S ↔ ∃ i : I, s X (ranges i) := by
    intro X
    constructor
    · intro hX
      obtain ⟨i, b, hi, hib, hXb⟩ := (hS X).mp hX
      let j : I := ⟨i, hi⟩
      have he := coded_function_value_unique C.rangesFunction hib (hrange j)
      exact ⟨j, he ▸ hXb⟩
    · rintro ⟨i, hXi⟩
      exact (hS X).mpr ⟨i.val, ranges i, i.property, hrange i, hXi⟩
  have hExists := fun i => transported_membership_graph base (hc i).1 (hc i).2.2.1
  let edges : I → U := fun i => Classical.choose (hExists i)
  have he : ∀ i, GraphCode s (ranges i) (edges i) ∧ ∀ X Y,
      CodedRelation s (edges i) X Y ↔ ∃ x y, CodedRelation s (codes i) x X ∧ CodedRelation s (codes i) y Y ∧ s y x :=
    fun i => Classical.choose_spec (hExists i)
  obtain ⟨e, hG, her⟩ := normalized_relation_comprehension base internalCopyEdgeFormula (cons G (cons C.codes Fin.elim0)) S
  have her' : ∀ X Y, CodedRelation s e X Y ↔ ∃ i : I, CodedRelation s (edges i) X Y := by
    intro X Y
    rw [her, eval_internalCopyEdgeFormula]
    constructor
    · rintro ⟨_, _, i, k, x, y, hi, hik, hxX, hyY, hyx⟩
      let j : I := ⟨i, hi⟩
      have hk := coded_function_value_unique C.codesFunction hik (hcode j)
      subst k
      exact ⟨j, ((he j).2 X Y).mpr ⟨x, y, hxX, hyY, hyx⟩⟩
    · rintro ⟨i, hXY⟩
      obtain ⟨x, y, hxX, hyY, hyx⟩ := ((he i).2 X Y).mp hXY
      exact ⟨(hS' X).mpr ⟨i, ((hc i).2.2.1 X).mpr ⟨x, coded_function_domain (hc i).1 hxX, hxX⟩⟩,
        (hS' Y).mpr ⟨i, ((hc i).2.2.1 Y).mpr ⟨y, coded_function_domain (hc i).1 hyY, hyY⟩⟩,
        i.val, codes i, x, y, i.property, hcode i, hxX, hyY, hyx⟩
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
  have hClosed : ∀ i, GraphClosedCode s S e (ranges i) := by
    intro i
    exact ⟨fun X hX => (hS' X).mpr ⟨i, hX⟩,
      fun X hX Y hXY => (graphCode_endpoints (he i).1 ((hRow i X hX Y).mp hXY)).2⟩
  have hEdges : ∀ i x y X Y, CodedRelation s (codes i) x X → CodedRelation s (codes i) y Y →
      (CodedRelation s e X Y ↔ s y x) := by
    intro i x y X Y hxX hyY
    have hX := ((hc i).2.2.1 X).mpr ⟨x, coded_function_domain (hc i).1 hxX, hxX⟩
    exact (hRow i X hX Y).trans (transported_membership_edge_iff (hc i).2.1 (he i).2 hxX hyY)
  refine ⟨⟨C, S, e, hS, hG, hEnd, ?_, ?_⟩⟩
  · intro i b hib
    let j : I := ⟨i, coded_function_domain C.rangesFunction hib⟩
    have heq := coded_function_value_unique C.rangesFunction hib (hrange j)
    exact heq.symm ▸ hClosed j
  · intro i k hik x y X Y hxX hyY
    let j : I := ⟨i, coded_function_domain C.codesFunction hik⟩
    have heq := coded_function_value_unique C.codesFunction hik (hcode j)
    exact hEdges j x y X Y (heq ▸ hxX) (heq ▸ hyY)

#print axioms internal_membership_amalgam
end FullBridge
