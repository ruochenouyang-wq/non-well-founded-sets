import SupportedPowerObstruction
namespace FullBridge
universe u v w
variable {U : Type u} {s : U → U → Prop}

/-- A larger-group action on a prescribed transitive core is compatible with
    the old subgroup action on a larger transitive domain. -/
def CoreActionCompatible {I : Type v} {J : Type w} {G : FiniteGroupData I} {H : FiniteGroupData J}
    (f : FiniteGroupEmbedding G H) (P : TransitiveGroupAction s G) (Q : TransitiveGroupAction s H) : Prop :=
  Subset s Q.domain P.domain ∧ ∀ g x y,
    CodedRelation s (Q.code (f.map g)) x y → CodedRelation s (P.code g) x y

theorem compatible_subgroup_action_restriction {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} {f : FiniteGroupEmbedding G H}
    {P : TransitiveGroupAction s G} {Q : TransitiveGroupAction s H}
    (hPQ : CoreActionCompatible f P Q) {g : I} {x y : U}
    (hx : s x Q.domain) (hxy : CodedRelation s (P.code g) x y) :
    CodedRelation s (Q.code (f.map g)) x y := by
  obtain ⟨z, hxz, _⟩ := (Q.iso (f.map g)).1.2 x hx
  have he := coded_function_value_unique (P.iso g).1 hxy (hPQ.2 g x z hxz)
  exact he.symm ▸ hxz

/-- All twisted copy transitions agree with the prescribed larger-group
    action on their shared core. This is the overlap needed for gluing. -/
theorem relative_induced_transition_on_core {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (P : TransitiveGroupAction s G) (Q : TransitiveGroupAction s H)
    (hPQ : CoreActionCompatible f P Q) (ranges codes : SubgroupCoset f → U)
    (hc : ∀ c, CopyCode s Q.domain P.domain (Q.code (cosetRepresentative f c)) (ranges c) (codes c))
    {h : J} {c : SubgroupCoset f} {x y X Y : U} (hX : s X Q.domain)
    (hxX : CodedRelation s (codes c) x X)
    (hxy : CodedRelation s (P.code (cosetFactor f h c)) x y)
    (hyY : CodedRelation s (codes (cosetAction f h c)) y Y) : CodedRelation s (Q.code h) X Y := by
  obtain ⟨x', hx', hx'X⟩ := ((Q.iso (cosetRepresentative f c)).2.2.1 X).mp hX
  have hxx' := (hc c).2.1 x x' X hxX ((hc c).2.2.2.2 x' X hx'X)
  subst x'
  have hxyQ := compatible_subgroup_action_restriction hPQ hx' hxy
  have hyt := ((Q.iso (f.map (cosetFactor f h c))).2.2.1 y).mpr ⟨x, hx', hxyQ⟩
  obtain ⟨Y', hyY', _⟩ := (Q.iso (cosetRepresentative f (cosetAction f h c))).1.2 y hyt
  have hYY' := coded_function_value_unique (hc (cosetAction f h c)).1 hyY
    ((hc (cosetAction f h c)).2.2.2.2 y Y' hyY')
  subst Y'
  have hprod := (Q.multiplication (cosetRepresentative f (cosetAction f h c))
    (f.map (cosetFactor f h c)) x Y).mpr ⟨y, hxyQ, hyY'⟩
  rw [← coset_factor_spec] at hprod
  obtain ⟨Z, hxZ, hZY⟩ := (Q.multiplication h (cosetRepresentative f c) x Y).mp hprod
  have hZX := coded_function_value_unique (Q.iso (cosetRepresentative f c)).1 hxZ hx'X
  exact hZX ▸ hZY

theorem relative_induced_action_functions (base : BaseCollection s) {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (P : TransitiveGroupAction s G) (Q : TransitiveGroupAction s H)
    (hPQ : CoreActionCompatible f P Q) {S : U}
    (ranges codes : SubgroupCoset f → U)
    (hc : ∀ c, CopyCode s Q.domain P.domain (Q.code (cosetRepresentative f c)) (ranges c) (codes c))
    (hInt : ∀ c d, c ≠ d → ∀ X, s X (ranges c) ∧ s X (ranges d) ↔ s X Q.domain)
    (hS : ∀ X, s X S ↔ ∃ c, s X (ranges c)) :
    ∃ rho : J → U, ∀ h, FunctionCode s S (rho h) ∧
      (∀ X Y, CodedRelation s (rho h) X Y ↔ ∃ c x y,
        CodedRelation s (codes c) x X ∧ CodedRelation s (P.code (cosetFactor f h c)) x y ∧
          CodedRelation s (codes (cosetAction f h c)) y Y) ∧
      (∀ X Y, s X Q.domain → CodedRelation s (rho h) X Y → CodedRelation s (Q.code h) X Y) := by
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
  have hCore : ∀ h X Y, s X Q.domain → CodedRelation s (rho h) X Y → CodedRelation s (Q.code h) X Y := by
    intro h X Y hX hXY
    obtain ⟨c, x, y, hxX, hxy, hyY⟩ := (hRel h X Y).mp hXY
    exact relative_induced_transition_on_core f P Q hPQ ranges codes hc hX hxX hxy hyY
  refine ⟨rho, fun h => ⟨?_, hRel h, hCore h⟩⟩
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
    by_cases hdc : d = c
    · subst d
      exact coded_function_value_unique (htrSpec h c).1
        (((htrSpec h c).2 X Z).mpr ⟨x, y, hxX, hxy, hyZ⟩) hXY
    · have hXt := (hInt d c hdc X).mp ⟨hXd, hXc⟩
      exact coded_function_value_unique (Q.iso h).1 (hCore h X Z hXt hXZ) (hCore h X Y hXt hXY')

#print axioms relative_induced_action_functions
end FullBridge
