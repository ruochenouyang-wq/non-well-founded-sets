import JointBoundaryRealizations
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem orbit_diagram_coded_graph_action (base : BaseCollection s) {w O : U}
    {J : InternalMask s w → U → U} (P : CodedMaskAction base w)
    (D : CodedOrbitDiagram base w J O) :
    ∃ Q : CodedMaskGraphAction base P D.domain D.edge, Q.maps = D.maps ∧
      ∀ i x y, CodedRelation s (Q.maps i) x y ↔ s x D.domain ∧ J i x = y := by
  have hm : P.masks = D.joint.masks := by
    apply base.extensional
    intro x
    exact (P.maskMembers x).trans (D.joint.maskMembers x).symm
  let Q : CodedMaskGraphAction base P D.domain D.edge :=
    ⟨D.joint.family, hm.symm ▸ D.joint.familyFunction, D.maps, D.mapCodes, D.iso, D.one, D.mul⟩
  exact ⟨Q, rfl, fun i => (D.joint.graphs i (D.maps i) (D.mapCodes i)).2⟩

theorem orbit_boundary_action_compatible {w O N E A p q : U}
    {J : InternalMask s w → U → U} (B : OrbitBoundary s O N E) (i : InternalMask s w)
    (hj : ElementaryMap s s (J i)) (hO : ∀ p, s p O → s (J i p) O)
    (hp : ∀ x y, CodedRelation s p x y ↔ s x A ∧ J i x = y)
    (hq : ∀ x y, CodedRelation s q x y ↔ s x N ∧ J i x = y) :
    BoundaryActionCompatible s B.code p q := by
  intro x y X Y hxy hxX hXY
  have h := orbit_boundary_equivariant hj B hO x X hxX
  exact ((hq x y).mp hxy).2 ▸ ((hp X Y).mp hXY).2 ▸ h

theorem joint_boundary_component_solution (base : BaseCollection s)
    {w O N E p t a r : U} (P : CodedMaskAction base w)
    (Q : CodedMaskGraphAction base P N E) (B : OrbitBoundary s O N E)
    {K : BoundaryRenaming s B.domain N B.code P.domain}
    {F : BoundaryGraphAttachment s B.domain N E B.code P.domain K}
    (R : JointBoundaryRealization base P Q K F) (C : OrbitDiagramComponent s N E p a r)
    (hp : s p O) (hpar : OrbitGraphParameters s p t a r)
    (hExt : GraphExtensionalCode s a r) (hta : Subset s t a) (htP : Subset s t P.domain) :
    ∃ f, DecorationCode s a r f ∧ InjectiveCode s f ∧
      (∀ x, s x t → CodedRelation s f x x) ∧
      (∀ x X, CodedRelation s f x X ↔ ∃ u, CodedRelation s C.code x u ∧ CodedRelation s R.function u X) := by
  obtain ⟨T, hT⟩ := attached_orbit_component_exists base B C K F hExt
  have hTfix := attached_orbit_component_fixes_old B C K hp hpar hta T hT
  obtain ⟨f, hf, hfr⟩ := closed_graph_copy_decoration_pullback base T R.solution
  refine ⟨f, hf, closed_graph_copy_least_pullback_injective base T R.least R.exactKernel hfr,
    fun x hx => (hfr x x).mpr ⟨x, hTfix x hx, R.fixed x (htP x hx)⟩, ?_⟩
  intro x X
  constructor
  · intro hxX
    obtain ⟨v, hxv, hvX⟩ := (hfr x X).mp hxX
    obtain ⟨u, hxu, huv⟩ := (hT x v).mp hxv
    exact ⟨u, hxu, (R.composite u X).mpr ⟨v, huv, hvX⟩⟩
  · rintro ⟨u, hxu, huX⟩
    obtain ⟨v, huv, hvX⟩ := (R.composite u X).mp huX
    exact (hfr x X).mpr ⟨v, (hT x v).mpr ⟨u, hxu, huv⟩, hvX⟩

structure JointOrbitRealization (base : BaseCollection s) {w O : U}
    {J : InternalMask s w → U → U} (P : CodedMaskAction base w)
    (D : CodedOrbitDiagram base w J O) where
  action : CodedMaskAction base w
  extendsOld : CodedMaskExtends base P action
  masksEqual : action.masks = P.masks
  function : U
  solution : DecorationCode s D.domain D.edge function
  values : ∀ x X, CodedRelation s function x X → s X action.domain
  equivariant : ∀ i x y X Y, CodedRelation s (D.maps i) x y →
    CodedRelation s function x X → CodedRelation s function y Y → CodedRelation s (action.maps i) X Y
  requests : ∀ p t a r, s p O → OrbitGraphParameters s p t a r →
    ∃ C : OrbitDiagramComponent s D.domain D.edge p a r, ∃ f,
      DecorationCode s a r f ∧ InjectiveCode s f ∧
      (∀ x, s x t → CodedRelation s f x x) ∧
      (∀ x X, CodedRelation s f x X ↔ ∃ u, CodedRelation s C.code x u ∧ CodedRelation s function u X)

theorem bafa_joint_orbit_realization (base : BaseCollection s) (hBAFA : BAFACode s)
    {w O : U} {J : InternalMask s w → U → U} (P : CodedMaskAction base w)
    (D : CodedOrbitDiagram base w J O)
    (hj : ∀ i, ElementaryMap s s (J i)) (hOA : Subset s O P.domain)
    (hO : ∀ i p, s p O → s (J i p) O) (hReq : ∀ p, s p O → BafaRequestCode s p)
    (hP : ∀ i x y, CodedRelation s (P.maps i) x y ↔ s x P.domain ∧ J i x = y) :
    Nonempty (JointOrbitRealization base P D) := by
  obtain ⟨Q, hQD, hQ⟩ := orbit_diagram_coded_graph_action base P D
  obtain ⟨B⟩ := orbit_boundary_exists base D.nodes D.edges hReq
  have htP : ∀ p t a r, s p O → OrbitGraphParameters s p t a r → Subset s t P.domain := by
    intro p t a r hp hpar x hx
    exact P.transitive t (orbit_graph_parameters_in_transitive P.transitive (hOA p hp) hpar).1 x hx
  have hbP := orbit_boundary_values_in_old B htP
  obtain ⟨K⟩ := boundary_renaming_exists base B.decoration.1 B.closed.1 hbP
  obtain ⟨F⟩ := boundary_graph_attachment_exists base K P.transitive B.closed B.decoration hbP
  have hcomp : ∀ i, BoundaryActionCompatible s B.code (P.maps i) (Q.maps i) :=
    fun i => orbit_boundary_action_compatible B i (hj i) (hO i) (hP i) (hQ i)
  obtain ⟨R⟩ := bafa_joint_boundary_realization base hBAFA P Q F D.graph hbP hcomp
  refine ⟨⟨R.action, R.extendsOld, R.masksEqual, R.function, R.rawSolution, R.values, ?_, ?_⟩⟩
  · intro i x y X Y hxy hxX hyY
    exact R.equivariant i x y X Y (hQD.symm ▸ hxy) hxX hyY
  · intro p t a r hp hpar
    obtain ⟨C⟩ := D.components p t a r hp hpar
    have hpr := bafa_request_parameters (hReq p hp) hpar
    obtain ⟨f, hf⟩ := joint_boundary_component_solution base P Q B R C hp hpar hpr.2.2.1
      hpr.2.2.2.1 (htP p t a r hp hpar)
    exact ⟨C, f, hf⟩

#print axioms bafa_joint_orbit_realization
end FullBridge
