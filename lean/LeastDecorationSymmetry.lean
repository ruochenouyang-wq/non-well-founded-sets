import LeastKernelDecoration
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Free variables [second image, first image, decoration, graph symmetry]. -/
def decorationSymmetryImageFormula : Formula 4 :=
  .ex (.ex (.conj (relatedFormula 4 1 3)
    (.conj (relatedFormula 5 1 0) (relatedFormula 4 0 2))))

theorem eval_decorationSymmetryImageFormula (g p X Y : U) :
    Eval s decorationSymmetryImageFormula (cons Y (cons X (cons g (cons p Fin.elim0)))) ↔
      ∃ x y, CodedRelation s g x X ∧ CodedRelation s p x y ∧ CodedRelation s g y Y := by
  simp only [decorationSymmetryImageFormula, Eval, eval_relatedFormula]
  rfl

theorem decoration_symmetry_image_code (base : BaseCollection s) {a g T : U}
    (hg : FunctionCode s a g) (hT : RangeCode s a g T) (p : U) :
    ∃ P, GraphCode s T P ∧ ∀ X Y, CodedRelation s P X Y ↔
      ∃ x y, CodedRelation s g x X ∧ CodedRelation s p x y ∧ CodedRelation s g y Y := by
  obtain ⟨P, hG, hP⟩ := normalized_relation_comprehension base decorationSymmetryImageFormula
    (cons g (cons p Fin.elim0)) T
  refine ⟨P, hG, fun X Y => ?_⟩
  rw [hP, eval_decorationSymmetryImageFormula]
  constructor
  · exact fun h => h.2.2
  · rintro ⟨x, y, hxX, hxy, hyY⟩
    exact ⟨(hT X).mpr ⟨x, coded_function_domain hg hxX, hxX⟩,
      (hT Y).mpr ⟨y, coded_function_domain hg hyY, hyY⟩, x, y, hxX, hxy, hyY⟩

/-- A symmetry descends through this decoration because its kernel is exactly
    the least relation, whose equivariance has already been proved. -/
theorem least_decoration_involution_descends (base : BaseCollection s) {a e m g p T : U}
    (hG : GraphCode s a e) (hm : LeastGraphRelationCode s a e m)
    (hg : DecorationCode s a e g) (hT : RangeCode s a g T)
    (hker : ∀ x y X Y, CodedRelation s g x X → CodedRelation s g y Y →
      (X = Y ↔ CodedRelation s m x y))
    (hp : GraphIsoCode s a e a e p)
    (hs : ∀ x y, CodedRelation s p x y → CodedRelation s p y x) :
    ∃ P, MembershipIsoCode s T T P ∧
      (∀ X Y, CodedRelation s P X Y → CodedRelation s P Y X) ∧
      (∀ X Y, CodedRelation s P X Y ↔
        ∃ x y, CodedRelation s g x X ∧ CodedRelation s p x y ∧ CodedRelation s g y Y) := by
  obtain ⟨P, hPG, hP⟩ := decoration_symmetry_image_code base hg.1 hT p
  have hsym : ∀ X Y, CodedRelation s P X Y → CodedRelation s P Y X := by
    intro X Y h
    obtain ⟨x, y, hxX, hxy, hyY⟩ := (hP X Y).mp h
    exact (hP Y X).mpr ⟨y, x, hyY, hs x y hxy, hxX⟩
  have hFun : FunctionCode s T P := by
    constructor
    · intro z hz
      obtain ⟨X, Y, hX, _, hXY⟩ := hPG z hz
      exact ⟨X, Y, hX, hXY⟩
    · intro X hX
      obtain ⟨x, hx, hxX⟩ := (hT X).mp hX
      obtain ⟨y, hxy, _⟩ := hp.1.2 x hx
      have hy := graph_iso_value hp hxy
      obtain ⟨Y, hyY, _⟩ := hg.1.2 y hy
      refine ⟨Y, (hP X Y).mpr ⟨x, y, hxX, hxy, hyY⟩, ?_⟩
      intro Z hXZ
      obtain ⟨u, v, huX, huv, hvZ⟩ := (hP X Z).mp hXZ
      have hux := (hker u x X X huX hxX).mp rfl
      have hvy := least_relation_iso_forward base hG hp hm hm huv hxy hux
      exact (hker v y Z Y hvZ hyY).mpr hvy
  have hInj : InjectiveCode s P := by
    intro X Y Z hXZ hYZ
    exact coded_function_value_unique hFun (hsym X Z hXZ) (hsym Y Z hYZ)
  have hRange : RangeCode s T P T := by
    intro Y
    constructor
    · intro hY
      obtain ⟨X, hYX, _⟩ := hFun.2 Y hY
      have hXY := hsym Y X hYX
      exact ⟨X, coded_function_domain hFun hXY, hXY⟩
    · rintro ⟨X, _, hXY⟩
      exact coded_function_domain hFun (hsym X Y hXY)
  have hForward : ∀ X Y X' Y', CodedRelation s P X X' → CodedRelation s P Y Y' →
      s Y X → s Y' X' := by
    intro X Y X' Y' hXX' hYY' hYX
    obtain ⟨x, x', hxX, hxx', hx'X'⟩ := (hP X X').mp hXX'
    obtain ⟨y, y', hyY, hyy', hy'Y'⟩ := (hP Y Y').mp hYY'
    have hx := coded_function_domain hg.1 hxX
    obtain ⟨z, hz, hxz, hzY⟩ := (hg.2 x hx X hxX Y).mp hYX
    obtain ⟨z', hzz', _⟩ := hp.1.2 z hz
    have hz' := graph_iso_value hp hzz'
    obtain ⟨Z', hz'Z', _⟩ := hg.1.2 z' hz'
    have hzy := (hker z y Y Y hzY hyY).mp rfl
    have hz'y' := least_relation_iso_forward base hG hp hm hm hzz' hyy' hzy
    have hZ'Y' := (hker z' y' Z' Y' hz'Z' hy'Y').mpr hz'y'
    have hx'z' := (hp.2.2.2 x z x' z' hxx' hzz').mp hxz
    exact (hg.2 x' (coded_function_domain hg.1 hx'X') X' hx'X' Y').mpr
      ⟨z', hz', hx'z', hZ'Y' ▸ hz'Z'⟩
  refine ⟨P, ⟨hFun, hInj, hRange, ?_⟩, hsym, hP⟩
  intro X Y X' Y' hXX' hYY'
  exact ⟨hForward X Y X' Y' hXX' hYY',
    hForward X' Y' X Y (hsym X X' hXX') (hsym Y Y' hYY')⟩

#print axioms least_decoration_involution_descends
end FullBridge
