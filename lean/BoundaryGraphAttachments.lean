import BoundaryRenamings
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

structure BoundaryGraphAttachment (s : U → U → Prop) (D N E b A : U)
    (K : BoundaryRenaming s D N b A) where
  domain : U
  edge : U
  members : ∀ X, s X domain ↔ s X A ∨ s X K.domain
  graph : GraphCode s domain edge
  old : EndExtensionCode s domain edge A
  rows : ∀ x X, CodedRelation s K.code x X → ∀ Y,
    CodedRelation s edge X Y ↔ ∃ y, CodedRelation s E x y ∧ CodedRelation s K.code y Y
  closed : GraphClosedCode s domain edge K.domain

/-- Glue a closed partial decoration to the literal old transitive set.
    Boundary nodes may be identified across components, not inside one. -/
theorem boundary_graph_attachment_exists (base : BaseCollection s) {D N E b A : U}
    (K : BoundaryRenaming s D N b A) (hA : TransitiveCode s A)
    (hD : GraphClosedCode s N E D) (hb : DecorationCode s D E b)
    (hOld : ∀ x X, CodedRelation s b x X → s X A) :
    Nonempty (BoundaryGraphAttachment s D N E b A K) := by
  obtain ⟨eB, heBG, heB⟩ := transported_relation_graph base K.function K.range (r := E)
  have himgOld : ∀ X, s X A → ∀ Y, CodedRelation s eB X Y → s Y X := by
    intro X hX Y hXY
    obtain ⟨x, y, hxX, hyY, hxy⟩ := (heB X Y).mp hXY
    have hbxX := K.old x X hxX hX
    have hxD := coded_function_domain hb.1 hbxX
    have hyD := hD.2 x hxD y hxy
    have hbyY := boundary_renaming_on_boundary K hb.1 hyD hyY
    exact (hb.2 x hxD X hbxX Y).mpr ⟨y, hyD, hxy, hbyY⟩
  have hback : ∀ x X, CodedRelation s b x X → ∀ Y, s Y X →
      ∃ y, CodedRelation s E x y ∧ CodedRelation s K.code y Y := by
    intro x X hxX Y hYX
    obtain ⟨y, _, hxy, hyY⟩ := (hb.2 x (coded_function_domain hb.1 hxX) X hxX Y).mp hYX
    exact ⟨y, hxy, K.extend y Y hyY⟩
  obtain ⟨eA, _, heAG, _, heA, _⟩ := membership_graph_identity_decoration base hA
  obtain ⟨S, hS⟩ := binary_union_exists base.pairing base.union A K.domain
  obtain ⟨e, hem, her⟩ := coded_relation_union base eA eB
  have heG : GraphCode s S e := by
    intro z hz
    rcases (hem z).mp hz with hza | hzb
    · obtain ⟨X, Y, hX, hY, hxy⟩ := heAG z hza
      exact ⟨X, Y, (hS X).mpr (Or.inl hX), (hS Y).mpr (Or.inl hY), hxy⟩
    · obtain ⟨X, Y, hX, hY, hxy⟩ := heBG z hzb
      exact ⟨X, Y, (hS X).mpr (Or.inr hX), (hS Y).mpr (Or.inr hY), hxy⟩
  have hrows : ∀ x X, CodedRelation s K.code x X → ∀ Y,
      CodedRelation s e X Y ↔ ∃ y, CodedRelation s E x y ∧ CodedRelation s K.code y Y := by
    intro x X hxX Y
    rw [her]
    constructor
    · rintro (hXY | hXY)
      · obtain ⟨hX, hYX⟩ := (heA X Y).mp hXY
        exact hback x X (K.old x X hxX hX) Y hYX
      · obtain ⟨x', y, hx'X, hyY, hx'y⟩ := (heB X Y).mp hXY
        rcases K.collision x' x X hx'X hxX with heq | ⟨hb', hbx⟩
        · exact ⟨y, heq ▸ hx'y, hyY⟩
        · have hX := hOld x' X hb'
          exact hback x X hbx Y (himgOld X hX Y ((heB X Y).mpr ⟨x', y, hx'X, hyY, hx'y⟩))
    · rintro ⟨y, hxy, hyY⟩
      exact Or.inr ((heB X Y).mpr ⟨x, y, hxX, hyY, hxy⟩)
  have hEnd : EndExtensionCode s S e A := by
    refine ⟨fun X hX => (hS X).mpr (Or.inl hX), fun X hX Y => ?_⟩
    rw [her]
    exact ⟨fun h => h.elim (fun h => ((heA X Y).mp h).2) (himgOld X hX Y),
      fun h => Or.inl ((heA X Y).mpr ⟨hX, h⟩)⟩
  refine ⟨⟨S, e, hS, heG, hEnd, hrows, ?_⟩⟩
  refine ⟨fun X hX => (hS X).mpr (Or.inr hX), ?_⟩
  intro X hX Y hXY
  obtain ⟨x, _, hxX⟩ := (K.range X).mp hX
  obtain ⟨y, _, hyY⟩ := (hrows x X hxX Y).mp hXY
  exact (K.range Y).mpr ⟨y, coded_function_domain K.function hyY, hyY⟩

/-- Composing any decoration of the glued graph really extends the prescribed boundary. -/
theorem boundary_attachment_decoration_pullback (base : BaseCollection s) {D N E b A g : U}
    {K : BoundaryRenaming s D N b A} (F : BoundaryGraphAttachment s D N E b A K)
    (hG : GraphCode s N E) (hg : DecorationCode s F.domain F.edge g)
    (hfix : ∀ X, s X A → CodedRelation s g X X)
    (hOld : ∀ x X, CodedRelation s b x X → s X A) :
    ∃ f, DecorationCode s N E f ∧
      (∀ x X, CodedRelation s f x X ↔ ∃ v, CodedRelation s K.code x v ∧ CodedRelation s g v X) ∧
      ∀ x X, CodedRelation s b x X → CodedRelation s f x X := by
  have hkS : ∀ x v, CodedRelation s K.code x v → s v F.domain :=
    fun x v h => F.closed.1 v ((K.range v).mpr ⟨x, coded_function_domain K.function h, h⟩)
  obtain ⟨f, hf, hfr⟩ := coded_functions_compose base K.function hg.1 hkS
  refine ⟨f, ⟨hf, ?_⟩, hfr, fun x X h =>
    (hfr x X).mpr ⟨X, K.extend x X h, hfix X (hOld x X h)⟩⟩
  intro x hx X hxX Y
  obtain ⟨v, hxv, hvX⟩ := (hfr x X).mp hxX
  constructor
  · intro hYX
    obtain ⟨u, _, hvu, huY⟩ := (hg.2 v (hkS x v hxv) X hvX Y).mp hYX
    obtain ⟨y, hxy, hyu⟩ := (F.rows x v hxv u).mp hvu
    exact ⟨y, (graphCode_endpoints hG hxy).2, hxy, (hfr y Y).mpr ⟨u, hyu, huY⟩⟩
  · rintro ⟨y, _, hxy, hyY⟩
    obtain ⟨u, hyu, huY⟩ := (hfr y Y).mp hyY
    exact (hg.2 v (hkS x v hxv) X hvX Y).mpr
      ⟨u, hkS y u hyu, (F.rows x v hxv u).mpr ⟨y, hxy, hyu⟩, huY⟩

#print axioms boundary_graph_attachment_exists
#print axioms boundary_attachment_decoration_pullback
end FullBridge
