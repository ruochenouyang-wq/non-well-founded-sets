import FiniteCosets
namespace FullBridge
universe u v w
variable {U : Type u} {s : U → U → Prop}

theorem twisted_copy_transition (base : BaseCollection s) {t A p q B C k l a : U}
    (hk : CopyCode s t A p B k) (hl : CopyCode s t A q C l)
    (ha : FunctionCode s A a) (har : RangeCode s A a A) :
    ∃ r, FunctionCode s B r ∧ ∀ X Y, CodedRelation s r X Y ↔
      ∃ x y, CodedRelation s k x X ∧ CodedRelation s a x y ∧ CodedRelation s l y Y := by
  obtain ⟨inv, hi, _, hir, hinv⟩ := coded_bijection_inverse base hk.1 hk.2.1 hk.2.2.1
  obtain ⟨b, hb, hbr⟩ := coded_functions_compose base hi ha
    (fun X x h => (hir x).mpr ⟨X, coded_function_domain hi h, h⟩)
  have hbA : ∀ X y, CodedRelation s b X y → s y A := by
    intro X y h
    obtain ⟨x, _, hxy⟩ := (hbr X y).mp h
    exact (har y).mpr ⟨x, coded_function_domain ha hxy, hxy⟩
  obtain ⟨r, hr, hrr⟩ := coded_functions_compose base hb hl.1 hbA
  refine ⟨r, hr, fun X Y => ?_⟩
  constructor
  · intro h
    obtain ⟨y, hXy, hyY⟩ := (hrr X Y).mp h
    obtain ⟨x, hXx, hxy⟩ := (hbr X y).mp hXy
    exact ⟨x, y, (hinv X x).mp hXx, hxy, hyY⟩
  · rintro ⟨x, y, hxX, hxy, hyY⟩
    exact (hrr X Y).mpr ⟨y, (hbr X y).mpr ⟨x, (hinv X x).mpr hxX, hxy⟩, hyY⟩

/-- Actual function codes for an induced action on disjoint coset copies.
    The coset space, representatives, and correction factors were constructed
    in FiniteCosets; they are not assumed as an unproved interface. -/
theorem induced_action_functions (base : BaseCollection s) {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (P : TransitiveGroupAction s G) {empty S : U} (hEmpty : ∀ x, ¬s x empty)
    (ranges codes : SubgroupCoset f → U)
    (hc : ∀ c, CopyCode s empty P.domain empty (ranges c) (codes c))
    (hInt : ∀ c d, c ≠ d → ∀ X, s X (ranges c) ∧ s X (ranges d) ↔ s X empty)
    (hS : ∀ X, s X S ↔ ∃ c, s X (ranges c)) :
    ∃ rho : J → U, ∀ h, FunctionCode s S (rho h) ∧
      ∀ X Y, CodedRelation s (rho h) X Y ↔ ∃ c x y,
        CodedRelation s (codes c) x X ∧ CodedRelation s (P.code (cosetFactor f h c)) x y ∧
          CodedRelation s (codes (cosetAction f h c)) y Y := by
  classical
  have htr := fun h c => twisted_copy_transition base (hc c) (hc (cosetAction f h c))
    (P.iso (cosetFactor f h c)).1 (P.iso (cosetFactor f h c)).2.2.1
  let tr : J → SubgroupCoset f → U := fun h c => Classical.choose (htr h c)
  have htrSpec := fun h c => Classical.choose_spec (htr h c)
  have hu := fun h => finite_indexed_relation_union base (cosetIndices f) (tr h)
  let rho : J → U := fun h => Classical.choose (hu h)
  have huSpec := fun h => Classical.choose_spec (hu h)
  have hRel : ∀ h X Y, CodedRelation s (rho h) X Y ↔ ∃ c x y,
      CodedRelation s (codes c) x X ∧ CodedRelation s (P.code (cosetFactor f h c)) x y ∧
        CodedRelation s (codes (cosetAction f h c)) y Y := by
    intro h X Y
    constructor
    · intro hXY
      obtain ⟨c, _, hXYc⟩ := ((huSpec h).2 X Y).mp hXY
      obtain ⟨x, y, hxX, hxy, hyY⟩ := ((htrSpec h c).2 X Y).mp hXYc
      exact ⟨c, x, y, hxX, hxy, hyY⟩
    · rintro ⟨c, x, y, hxX, hxy, hyY⟩
      exact ((huSpec h).2 X Y).mpr ⟨c, coset_indices_complete f c,
        ((htrSpec h c).2 X Y).mpr ⟨x, y, hxX, hxy, hyY⟩⟩
  refine ⟨rho, fun h => ⟨?_, hRel h⟩⟩
  constructor
  · intro z hz
    obtain ⟨c, _, hzc⟩ := ((huSpec h).1 z).mp hz
    obtain ⟨X, Y, hX, hXY⟩ := (htrSpec h c).1.1 z hzc
    exact ⟨X, Y, (hS X).mpr ⟨c, hX⟩, hXY⟩
  · intro X hX
    obtain ⟨c, hXc⟩ := (hS X).mp hX
    obtain ⟨Y, hXY, _⟩ := (htrSpec h c).1.2 X hXc
    have hXY' := (hRel h X Y).mpr (by
      obtain ⟨x, y, hxX, hxy, hyY⟩ := ((htrSpec h c).2 X Y).mp hXY
      exact ⟨c, x, y, hxX, hxy, hyY⟩)
    refine ⟨Y, hXY', ?_⟩
    intro Z hXZ
    obtain ⟨d, x, y, hxX, hxy, hyZ⟩ := (hRel h X Z).mp hXZ
    have hXd := ((hc d).2.2.1 X).mpr ⟨x, coded_function_domain (hc d).1 hxX, hxX⟩
    have hdc : d = c := by
      by_cases hdc : d = c
      · exact hdc
      · exact False.elim (hEmpty X ((hInt d c hdc X).mp ⟨hXd, hXc⟩))
    subst d
    exact coded_function_value_unique (htrSpec h c).1
      (((htrSpec h c).2 X Z).mpr ⟨x, y, hxX, hxy, hyZ⟩) hXY

#print axioms induced_action_functions
end FullBridge
