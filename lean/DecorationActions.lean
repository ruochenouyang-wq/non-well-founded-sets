import CountableBafaInvolutions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def DecorationImageCode (s : U → U → Prop) (g p P : U) : Prop :=
  ∀ X Y, CodedRelation s P X Y ↔
    ∃ x y, CodedRelation s g x X ∧ CodedRelation s p x y ∧ CodedRelation s g y Y

/-- General automorphisms descend through the same least-kernel decoration;
    neither an involution hypothesis nor injectivity of the decoration is needed. -/
theorem least_decoration_automorphism_descends (base : BaseCollection s) {a e m g p T : U}
    (hG : GraphCode s a e) (hm : LeastGraphRelationCode s a e m)
    (hg : DecorationCode s a e g) (hT : RangeCode s a g T)
    (hker : ∀ x y X Y, CodedRelation s g x X → CodedRelation s g y Y →
      (X = Y ↔ CodedRelation s m x y))
    (hp : GraphIsoCode s a e a e p) :
    ∃ P, MembershipIsoCode s T T P ∧ DecorationImageCode s g p P := by
  obtain ⟨P, hPG, hP⟩ := decoration_symmetry_image_code base hg.1 hT p
  have hFun : FunctionCode s T P := by
    constructor
    · intro z hz
      obtain ⟨X, Y, hX, _, hXY⟩ := hPG z hz
      exact ⟨X, Y, hX, hXY⟩
    · intro X hX
      obtain ⟨x, hx, hxX⟩ := (hT X).mp hX
      obtain ⟨y, hxy, _⟩ := hp.1.2 x hx
      obtain ⟨Y, hyY, _⟩ := hg.1.2 y (graph_iso_value hp hxy)
      refine ⟨Y, (hP X Y).mpr ⟨x, y, hxX, hxy, hyY⟩, ?_⟩
      intro Z hXZ
      obtain ⟨u, v, huX, huv, hvZ⟩ := (hP X Z).mp hXZ
      have hux := (hker u x X X huX hxX).mp rfl
      have hvy := least_relation_iso_forward base hG hp hm hm huv hxy hux
      exact (hker v y Z Y hvZ hyY).mpr hvy
  have hInj : InjectiveCode s P := by
    intro X Y Z hXZ hYZ
    obtain ⟨x, x', hxX, hxx', hx'Z⟩ := (hP X Z).mp hXZ
    obtain ⟨y, y', hyY, hyy', hy'Z⟩ := (hP Y Z).mp hYZ
    have hx'y' := (hker x' y' Z Z hx'Z hy'Z).mp rfl
    have hxy := (least_relation_iso_iff base hG hG hp hm hm hxx' hyy').mpr hx'y'
    exact (hker x y X Y hxX hyY).mpr hxy
  have hRange : RangeCode s T P T := by
    intro Y
    constructor
    · intro hY
      obtain ⟨y, hy, hyY⟩ := (hT Y).mp hY
      obtain ⟨x, hx, hxy⟩ := (hp.2.2.1 y).mp hy
      obtain ⟨X, hxX, _⟩ := hg.1.2 x hx
      exact ⟨X, (hT X).mpr ⟨x, hx, hxX⟩, (hP X Y).mpr ⟨x, y, hxX, hxy, hyY⟩⟩
    · rintro ⟨X, _, hXY⟩
      obtain ⟨x, y, _, _, hyY⟩ := (hP X Y).mp hXY
      exact (hT Y).mpr ⟨y, coded_function_domain hg.1 hyY, hyY⟩
  refine ⟨P, ⟨hFun, hInj, hRange, ?_⟩, hP⟩
  intro X Y X' Y' hXX' hYY'
  obtain ⟨x, x', hxX, hxx', hx'X'⟩ := (hP X X').mp hXX'
  obtain ⟨y, y', hyY, hyy', hy'Y'⟩ := (hP Y Y').mp hYY'
  constructor
  · intro hYX
    obtain ⟨z, hz, hxz, hzY⟩ :=
      (hg.2 x (coded_function_domain hg.1 hxX) X hxX Y).mp hYX
    obtain ⟨z', hzz', _⟩ := hp.1.2 z hz
    have hz' := graph_iso_value hp hzz'
    obtain ⟨Z', hz'Z', _⟩ := hg.1.2 z' hz'
    have hzy := (hker z y Y Y hzY hyY).mp rfl
    have hz'y' := least_relation_iso_forward base hG hp hm hm hzz' hyy' hzy
    have hZ'Y' := (hker z' y' Z' Y' hz'Z' hy'Y').mpr hz'y'
    exact (hg.2 x' (coded_function_domain hg.1 hx'X') X' hx'X' Y').mpr
      ⟨z', hz', (hp.2.2.2 x z x' z' hxx' hzz').mp hxz, hZ'Y' ▸ hz'Z'⟩
  · intro hY'X'
    obtain ⟨z', hz', hx'z', hz'Y'⟩ :=
      (hg.2 x' (coded_function_domain hg.1 hx'X') X' hx'X' Y').mp hY'X'
    obtain ⟨z, hz, hzz'⟩ := (hp.2.2.1 z').mp hz'
    obtain ⟨Z, hzZ, _⟩ := hg.1.2 z hz
    have hz'y' := (hker z' y' Y' Y' hz'Y' hy'Y').mp rfl
    have hzy := (least_relation_iso_iff base hG hG hp hm hm hzz' hyy').mpr hz'y'
    have hZY := (hker z y Z Y hzZ hyY).mpr hzy
    exact (hg.2 x (coded_function_domain hg.1 hxX) X hxX Y).mpr
      ⟨z, hz, (hp.2.2.2 x z x' z' hxx' hzz').mpr hx'z', hZY ▸ hzZ⟩

#print axioms least_decoration_automorphism_descends
end FullBridge
