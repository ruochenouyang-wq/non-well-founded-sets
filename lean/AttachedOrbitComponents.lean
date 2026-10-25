import BoundaryGraphAttachments
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

structure ClosedGraphCopy (s : U → U → Prop) (N E a r : U) where
  domain : U
  code : U
  function : FunctionCode s a code
  injective : InjectiveCode s code
  range : RangeCode s a code domain
  closed : GraphClosedCode s N E domain
  transported : ∀ x y X Y, CodedRelation s code x X → CodedRelation s code y Y →
    (CodedRelation s E X Y ↔ CodedRelation s r x y)
  extensional : GraphExtensionalCode s domain E

theorem closed_graph_copy_decoration_pullback (base : BaseCollection s) {N E a r g : U}
    (C : ClosedGraphCopy s N E a r) (hg : DecorationCode s N E g) :
    ∃ f, DecorationCode s a r f ∧ ∀ x X, CodedRelation s f x X ↔
      ∃ v, CodedRelation s C.code x v ∧ CodedRelation s g v X := by
  have hcN : ∀ x v, CodedRelation s C.code x v → s v N := fun x v h =>
    C.closed.1 v ((C.range v).mpr ⟨x, coded_function_domain C.function h, h⟩)
  obtain ⟨f, hf, hfr⟩ := coded_functions_compose base C.function hg.1 hcN
  refine ⟨f, ⟨hf, ?_⟩, hfr⟩
  intro x hx X hxX Y
  obtain ⟨v, hxv, hvX⟩ := (hfr x X).mp hxX
  constructor
  · intro hYX
    obtain ⟨u, _, hvu, huY⟩ := (hg.2 v (hcN x v hxv) X hvX Y).mp hYX
    obtain ⟨y, hy, hyu⟩ := (C.range u).mp
      (C.closed.2 v ((C.range v).mpr ⟨x, hx, hxv⟩) u hvu)
    exact ⟨y, hy, (C.transported x y v u hxv hyu).mp hvu, (hfr y Y).mpr ⟨u, hyu, huY⟩⟩
  · rintro ⟨y, _, hxy, hyY⟩
    obtain ⟨u, hyu, huY⟩ := (hfr y Y).mp hyY
    exact (hg.2 v (hcN x v hxv) X hvX Y).mpr
      ⟨u, hcN y u hyu, (C.transported x y v u hxv hyu).mpr hxy, huY⟩

theorem closed_graph_copy_least_pullback_injective (base : BaseCollection s)
    {N E a r m g f : U} (C : ClosedGraphCopy s N E a r)
    (hm : LeastGraphRelationCode s N E m)
    (hker : ∀ x y X Y, CodedRelation s g x X → CodedRelation s g y Y →
      (X = Y ↔ CodedRelation s m x y))
    (hfr : ∀ x X, CodedRelation s f x X ↔
      ∃ v, CodedRelation s C.code x v ∧ CodedRelation s g v X) : InjectiveCode s f := by
  intro x y Z hxZ hyZ
  obtain ⟨X, hxX, hXZ⟩ := (hfr x Z).mp hxZ
  obtain ⟨Y, hyY, hYZ⟩ := (hfr y Z).mp hyZ
  have hX := (C.range X).mpr ⟨x, coded_function_domain C.function hxX, hxX⟩
  have hY := (C.range Y).mpr ⟨y, coded_function_domain C.function hyY, hyY⟩
  have hXY := least_relation_preserves_closed_extensional base C.closed C.extensional hm hX hY
    ((hker X Y Z Z hXZ hYZ).mp rfl)
  exact C.injective x y Y (hXY ▸ hxX) hyY

/-- Each component remains an injective closed extensional graph after boundary gluing. -/
theorem attached_orbit_component_exists (base : BaseCollection s) {O N E p a r A : U}
    (B : OrbitBoundary s O N E) (C : OrbitDiagramComponent s N E p a r)
    (K : BoundaryRenaming s B.domain N B.code A)
    (F : BoundaryGraphAttachment s B.domain N E B.code A K)
    (hExt : GraphExtensionalCode s a r) :
    ∃ Q : ClosedGraphCopy s F.domain F.edge a r, ∀ x X, CodedRelation s Q.code x X ↔
      ∃ u, CodedRelation s C.code x u ∧ CodedRelation s K.code u X := by
  have hcN : ∀ x u, CodedRelation s C.code x u → s u N := fun x u h =>
    C.closed.1 u ((C.range u).mpr ⟨x, coded_function_domain C.function h, h⟩)
  obtain ⟨k, hk, hkr⟩ := coded_functions_compose base C.function K.function hcN
  obtain ⟨d, hd⟩ := coded_image_set_exists base k a
  have hkI : InjectiveCode s k := by
    intro x y Z hxZ hyZ
    obtain ⟨X, hxX, hXZ⟩ := (hkr x Z).mp hxZ
    obtain ⟨Y, hyY, hYZ⟩ := (hkr y Z).mp hyZ
    have hXY := orbit_boundary_renaming_component_injective base B C K X Y Z
      ((C.range X).mpr ⟨x, coded_function_domain C.function hxX, hxX⟩)
      ((C.range Y).mpr ⟨y, coded_function_domain C.function hyY, hyY⟩) hXZ hYZ
    exact C.injective x y Y (hXY ▸ hxX) hyY
  have hclosed : GraphClosedCode s F.domain F.edge d := by
    constructor
    · intro X hX
      obtain ⟨x, _, hxX⟩ := (hd X).mp hX
      obtain ⟨u, _, huX⟩ := (hkr x X).mp hxX
      exact F.closed.1 X ((K.range X).mpr ⟨u, coded_function_domain K.function huX, huX⟩)
    · intro X hX Y hXY
      obtain ⟨x, hx, hxX⟩ := (hd X).mp hX
      obtain ⟨u, hxu, huX⟩ := (hkr x X).mp hxX
      obtain ⟨v, huv, hvY⟩ := (F.rows u X huX Y).mp hXY
      obtain ⟨y, hy, hyv⟩ := (C.range v).mp
        (C.closed.2 u ((C.range u).mpr ⟨x, hx, hxu⟩) v huv)
      exact (hd Y).mpr ⟨y, hy, (hkr y Y).mpr ⟨v, hyv, hvY⟩⟩
  have htransport : ∀ x y X Y, CodedRelation s k x X → CodedRelation s k y Y →
      (CodedRelation s F.edge X Y ↔ CodedRelation s r x y) := by
    intro x y X Y hxX hyY
    obtain ⟨u, hxu, huX⟩ := (hkr x X).mp hxX
    obtain ⟨v, hyv, hvY⟩ := (hkr y Y).mp hyY
    constructor
    · intro hXY
      obtain ⟨v', huv', hv'Y⟩ := (F.rows u X huX Y).mp hXY
      have hu := (C.range u).mpr ⟨x, coded_function_domain C.function hxu, hxu⟩
      have hv := (C.range v).mpr ⟨y, coded_function_domain C.function hyv, hyv⟩
      have hvv := orbit_boundary_renaming_component_injective base B C K v' v Y
        (C.closed.2 u hu v' huv') hv hv'Y hvY
      exact (C.transported x y u v hxu hyv).mp (hvv ▸ huv')
    · intro hxy
      exact (F.rows u X huX Y).mpr ⟨v, (C.transported x y u v hxu hyv).mpr hxy, hvY⟩
  have hext : GraphExtensionalCode s d F.edge := by
    intro X hX Y hY hrows
    obtain ⟨x, hx, hxX⟩ := (hd X).mp hX
    obtain ⟨y, hy, hyY⟩ := (hd Y).mp hY
    have hxy : x = y := by
      apply hExt x hx y hy
      intro z hz
      obtain ⟨Z, hzZ, _⟩ := hk.2 z hz
      exact (htransport x z X Z hxX hzZ).symm.trans
        ((hrows Z ((hd Z).mpr ⟨z, hz, hzZ⟩)).trans (htransport y z Y Z hyY hzZ))
    subst y
    exact coded_function_value_unique hk hxX hyY
  exact ⟨⟨d, k, hk, hkI, hd, hclosed, htransport, hext⟩, hkr⟩

theorem attached_orbit_component_fixes_old {O N E p t a r A : U}
    (B : OrbitBoundary s O N E) (C : OrbitDiagramComponent s N E p a r)
    (K : BoundaryRenaming s B.domain N B.code A)
    (hp : s p O) (hpar : OrbitGraphParameters s p t a r) (hta : Subset s t a)
    {S e : U} (Q : ClosedGraphCopy s S e a r)
    (hQ : ∀ x X, CodedRelation s Q.code x X ↔
      ∃ u, CodedRelation s C.code x u ∧ CodedRelation s K.code u X) :
    ∀ x, s x t → CodedRelation s Q.code x x := by
  intro x hx
  obtain ⟨u, hxu, _⟩ := C.function.2 x (hta x hx)
  exact (hQ x x).mpr ⟨u, hxu,
    K.extend u x ((orbit_boundary_on_component B C hp hpar hxu).2 hx)⟩

#print axioms attached_orbit_component_exists
end FullBridge
