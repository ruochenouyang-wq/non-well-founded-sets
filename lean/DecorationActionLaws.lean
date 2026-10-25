import DecorationActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem decoration_image_unique (base : BaseCollection s) {g p T P Q : U}
    (hf : FunctionCode s T P) (hq : FunctionCode s T Q)
    (hP : DecorationImageCode s g p P) (hQ : DecorationImageCode s g p Q) : P = Q := by
  apply function_code_extensional base.extensional hf hq
  intro X Y Z hXY hXZ
  exact coded_function_value_unique hq ((hQ X Y).mpr ((hP X Y).mp hXY)) hXZ

theorem decoration_image_identity {a g p P : U} (hg : FunctionCode s a g)
    (hP : DecorationImageCode s g p P)
    (hid : ∀ x y, CodedRelation s p x y → x = y) :
    ∀ X Y, CodedRelation s P X Y → X = Y := by
  intro X Y hXY
  obtain ⟨x, y, hxX, hxy, hyY⟩ := (hP X Y).mp hXY
  exact coded_function_value_unique hg hxX ((hid x y hxy).symm ▸ hyY)

/-- Composition agrees as an actual coded relation, even when the decoration
    has a nontrivial kernel and the middle representatives differ. -/
theorem decoration_image_composition {a e g p q r T P Q R : U}
    (hg : FunctionCode s a g) (hp : GraphIsoCode s a e a e p)
    (hq : FunctionCode s a q) (hqr : RangeCode s a q a)
    (hQfun : FunctionCode s T Q)
    (hP : DecorationImageCode s g p P) (hQ : DecorationImageCode s g q Q)
    (hR : DecorationImageCode s g r R)
    (hcomp : ∀ x z, CodedRelation s r x z ↔
      ∃ y, CodedRelation s p x y ∧ CodedRelation s q y z) :
    ∀ X Z, CodedRelation s R X Z ↔
      ∃ Y, CodedRelation s P X Y ∧ CodedRelation s Q Y Z := by
  intro X Z
  constructor
  · intro hXZ
    obtain ⟨x, z, hxX, hxz, hzZ⟩ := (hR X Z).mp hXZ
    obtain ⟨y, hxy, hyz⟩ := (hcomp x z).mp hxz
    obtain ⟨Y, hyY, _⟩ := hg.2 y (graph_iso_value hp hxy)
    exact ⟨Y, (hP X Y).mpr ⟨x, y, hxX, hxy, hyY⟩,
      (hQ Y Z).mpr ⟨y, z, hyY, hyz, hzZ⟩⟩
  · rintro ⟨Y, hXY, hYZ⟩
    obtain ⟨x, y, hxX, hxy, hyY⟩ := (hP X Y).mp hXY
    obtain ⟨z, hyz, _⟩ := hq.2 y (graph_iso_value hp hxy)
    have hz := (hqr z).mpr ⟨y, graph_iso_value hp hxy, hyz⟩
    obtain ⟨Z', hzZ', _⟩ := hg.2 z hz
    have hYZ' := (hQ Y Z').mpr ⟨y, z, hyY, hyz, hzZ'⟩
    have hZ'Z := coded_function_value_unique hQfun hYZ' hYZ
    exact (hR X Z).mpr ⟨x, z, hxX, (hcomp x z).mpr ⟨y, hxy, hyz⟩, hZ'Z ▸ hzZ'⟩

theorem decoration_image_inverse {g p q P Q : U}
    (hP : DecorationImageCode s g p P) (hQ : DecorationImageCode s g q Q)
    (hinv : ∀ x y, CodedRelation s q y x ↔ CodedRelation s p x y) :
    ∀ X Y, CodedRelation s Q Y X ↔ CodedRelation s P X Y := by
  intro X Y
  constructor
  · intro hYX
    obtain ⟨y, x, hyY, hyx, hxX⟩ := (hQ Y X).mp hYX
    exact (hP X Y).mpr ⟨x, y, hxX, (hinv x y).mp hyx, hyY⟩
  · intro hXY
    obtain ⟨x, y, hxX, hxy, hyY⟩ := (hP X Y).mp hXY
    exact (hQ Y X).mpr ⟨y, x, hyY, (hinv x y).mpr hxy, hxX⟩

/-- Exact loss of action information: two images coincide precisely when their
    values at each common input are identified by the decoration kernel. -/
theorem decoration_images_equal_iff (base : BaseCollection s) {a e m g p q T P Q : U}
    (hg : FunctionCode s a g) (hp : GraphIsoCode s a e a e p)
    (hq : GraphIsoCode s a e a e q)
    (hPf : FunctionCode s T P) (hQf : FunctionCode s T Q)
    (hP : DecorationImageCode s g p P) (hQ : DecorationImageCode s g q Q)
    (hker : ∀ x y X Y, CodedRelation s g x X → CodedRelation s g y Y →
      (X = Y ↔ CodedRelation s m x y)) :
    P = Q ↔ ∀ x y z, CodedRelation s p x y → CodedRelation s q x z →
      CodedRelation s m y z := by
  constructor
  · intro hEq x y z hxy hxz
    obtain ⟨X, hxX, _⟩ := hg.2 x (coded_function_domain hp.1 hxy)
    obtain ⟨Y, hyY, _⟩ := hg.2 y (graph_iso_value hp hxy)
    obtain ⟨Z, hzZ, _⟩ := hg.2 z (graph_iso_value hq hxz)
    have hXY := (hP X Y).mpr ⟨x, y, hxX, hxy, hyY⟩
    have hXZ := (hQ X Z).mpr ⟨x, z, hxX, hxz, hzZ⟩
    exact (hker y z Y Z hyY hzZ).mp (coded_function_value_unique hQf (hEq ▸ hXY) hXZ)
  · intro h
    apply function_code_extensional base.extensional hPf hQf
    intro X Y Z hXY hXZ
    obtain ⟨x, y, hxX, hxy, hyY⟩ := (hP X Y).mp hXY
    obtain ⟨z, hxz, _⟩ := hq.1.2 x (coded_function_domain hp.1 hxy)
    obtain ⟨Z', hzZ', _⟩ := hg.2 z (graph_iso_value hq hxz)
    have hXZ' := (hQ X Z').mpr ⟨x, z, hxX, hxz, hzZ'⟩
    have hYZ' := (hker y z Y Z' hyY hzZ').mpr (h x y z hxy hxz)
    exact hYZ'.trans (coded_function_value_unique hQf hXZ' hXZ)

theorem decoration_image_identity_iff {a e m g p P : U}
    (hg : FunctionCode s a g) (hp : GraphIsoCode s a e a e p)
    (hP : DecorationImageCode s g p P)
    (hker : ∀ x y X Y, CodedRelation s g x X → CodedRelation s g y Y →
      (X = Y ↔ CodedRelation s m x y)) :
    (∀ X Y, CodedRelation s P X Y → X = Y) ↔
      ∀ x y, CodedRelation s p x y → CodedRelation s m x y := by
  constructor
  · intro h x y hxy
    obtain ⟨X, hxX, _⟩ := hg.2 x (coded_function_domain hp.1 hxy)
    obtain ⟨Y, hyY, _⟩ := hg.2 y (graph_iso_value hp hxy)
    exact (hker x y X Y hxX hyY).mp (h X Y ((hP X Y).mpr ⟨x, y, hxX, hxy, hyY⟩))
  · intro h X Y hXY
    obtain ⟨x, y, hxX, hxy, hyY⟩ := (hP X Y).mp hXY
    exact (hker x y X Y hxX hyY).mpr (h x y hxy)

#print axioms decoration_image_composition
#print axioms decoration_images_equal_iff
end FullBridge
