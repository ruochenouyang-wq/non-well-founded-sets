import OrbitDiagramInstances
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem orbit_component_decoration_pullback (base : BaseCollection s) {N E p a r g : U}
    (C : OrbitDiagramComponent s N E p a r) (hg : DecorationCode s N E g) :
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

theorem orbit_component_least_pullback_injective (base : BaseCollection s)
    {N E p a r m g f : U} (C : OrbitDiagramComponent s N E p a r)
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

/-- The boundary condition is explicit: a raw tagged diagram does not provide it. -/
theorem orbit_component_pullback_fixes_boundary {N E p t a r g f : U}
    (C : OrbitDiagramComponent s N E p a r) (hta : Subset s t a)
    (hfr : ∀ x X, CodedRelation s f x X ↔
      ∃ v, CodedRelation s C.code x v ∧ CodedRelation s g v X)
    (hboundary : ∀ x v, s x t → CodedRelation s C.code x v → CodedRelation s g v x) :
    ∀ x, s x t → CodedRelation s f x x := by
  intro x hx
  obtain ⟨v, hxv, _⟩ := C.function.2 x (hta x hx)
  exact (hfr x x).mpr ⟨v, hxv, hboundary x v hx hxv⟩

theorem orbit_component_pullback_equivariant (base : BaseCollection s) {j : U → U}
    (hj : ElementaryMap s s j) {N E p t a r g f : U}
    (C : OrbitDiagramComponent s N E p a r) (hp : OrbitGraphParameters s p t a r)
    (hfix : j p = p)
    (hfr : ∀ x X, CodedRelation s f x X ↔
      ∃ v, CodedRelation s C.code x v ∧ CodedRelation s g v X)
    (heq : ∀ v X, CodedRelation s g v X → CodedRelation s g (j v) (j X)) :
    ∀ x X, CodedRelation s f x X → CodedRelation s f (j x) (j X) := by
  have ha := ((graph_parameter_stabilizer_iff base hj hp).mp hfix).2.1
  intro x X hxX
  obtain ⟨v, hxv, hvX⟩ := (hfr x X).mp hxX
  obtain ⟨hx, hpv⟩ := (C.values x v).mp hxv
  have hjx : s (j x) a := by
    have h := (hj (Formula.member (n := 2) 0 1) (cons x (cons a Fin.elim0))).mp hx
    change s (j x) (j a) at h
    rwa [ha] at h
  have hpj := elementary_map_ordered_pair hj hpv
  rw [hfix] at hpj
  exact (hfr (j x) (j X)).mpr ⟨j v, (C.values (j x) (j v)).mpr ⟨hjx, hpj⟩, heq v X hvX⟩

theorem orbit_component_pullback_hereditary (base : BaseCollection s) {z w N E p t a r g f : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hs : ∀ i x, J i (J i x) = x)
    (C : OrbitDiagramComponent s N E p a r) (hp : OrbitGraphParameters s p t a r)
    (htH : HereditarilyMaskSupported s w J t) (haH : HereditarilyMaskSupported s w J a)
    (hrH : HereditarilyMaskSupported s w J r) (hf : DecorationCode s a r f)
    (hfr : ∀ x X, CodedRelation s f x X ↔
      ∃ v, CodedRelation s C.code x v ∧ CodedRelation s g v X)
    (heq : ∀ i v X, CodedRelation s g v X → CodedRelation s g (J i v) (J i X)) :
    HereditarilyMaskSupported s w J f ∧
      ∀ x X, CodedRelation s f x X → HereditarilyMaskSupported s w J X := by
  obtain ⟨K, hK, hpfix⟩ := hereditary_mask_root (hereditary_mask_graph_parameter base hw hj hp htH haH hrH)
  have htail : MaskTailEquivariantFunction s J f :=
    ⟨K, hK, fun i hi => orbit_component_pullback_equivariant base (hj i) C hp (hpfix i hi) hfr (heq i)⟩
  exact mask_equivariant_decoration_hereditary base hw hj hs hf htail
    (fun x hx => hereditary_mask_member haH hx)

#print axioms orbit_component_pullback_hereditary
end FullBridge
