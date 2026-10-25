import AttachedOrbitComponents
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- One common realization, fixing the literal old set, with an injective
    fixed-parameter solution for every orbit request. No support is asserted. -/
structure FixedOrbitRealization (s : U → U → Prop) (O A : U) where
  domain : U
  edge : U
  graph : GraphCode s domain edge
  old : EndExtensionCode s domain edge A
  decoration : U
  solution : DecorationCode s domain edge decoration
  fixed : ∀ x, s x A → CodedRelation s decoration x x
  requests : ∀ p t a r, s p O → OrbitGraphParameters s p t a r →
    ∃ Q : ClosedGraphCopy s domain edge a r, ∃ f,
      (∀ x, s x t → CodedRelation s Q.code x x) ∧
      DecorationCode s a r f ∧ InjectiveCode s f ∧
      (∀ x, s x t → CodedRelation s f x x) ∧
      (∀ x X, CodedRelation s f x X ↔
        ∃ u, CodedRelation s Q.code x u ∧ CodedRelation s decoration u X)

theorem bafa_fixed_orbit_realization (base : BaseCollection s) (hBAFA : BAFACode s)
    {O N E A : U} (hA : TransitiveCode s A)
    (hN : ∀ X, s X N ↔ OrbitDiagramNode s O X)
    (hE : ∀ X Y, CodedRelation s E X Y ↔ OrbitDiagramEdge s O X Y)
    (hReq : ∀ p, s p O → BafaRequestCode s p)
    (hOld : ∀ p t a r, s p O → OrbitGraphParameters s p t a r → Subset s t A) :
    Nonempty (FixedOrbitRealization s O A) := by
  obtain ⟨B⟩ := orbit_boundary_exists base hN hE hReq
  have hbA := orbit_boundary_values_in_old B hOld
  obtain ⟨K⟩ := boundary_renaming_exists base B.decoration.1 B.closed.1 hbA
  obtain ⟨F⟩ := boundary_graph_attachment_exists base K hA B.closed B.decoration hbA
  obtain ⟨m, g, hm, hg, hfix, hker⟩ := bafa_fixed_least_decoration base hBAFA hA F.graph F.old
  refine ⟨⟨F.domain, F.edge, F.graph, F.old, g, hg, hfix, ?_⟩⟩
  intro p t a r hp hpar
  have hpr := bafa_request_parameters (hReq p hp) hpar
  obtain ⟨C⟩ := orbit_diagram_component_exists base hN hE hp hpar (hReq p hp)
  obtain ⟨Q, hQ⟩ := attached_orbit_component_exists base B C K F hpr.2.2.1
  have hQfix := attached_orbit_component_fixes_old B C K hp hpar hpr.2.2.2.1 Q hQ
  obtain ⟨f, hf, hfr⟩ := closed_graph_copy_decoration_pullback base Q hg
  refine ⟨Q, f, hQfix, hf, closed_graph_copy_least_pullback_injective base Q hm hker hfr, ?_, hfr⟩
  intro x hx
  exact (hfr x x).mpr ⟨x, hQfix x hx, hfix x (hOld p t a r hp hpar x hx)⟩

theorem bafa_fixed_orbit_realization_of_bound (base : BaseCollection s) (hBAFA : BAFACode s)
    {w O A : U} {J : InternalMask s w → U → U} (D : CodedOrbitDiagram base w J O)
    (hA : TransitiveCode s A) (hOA : Subset s O A)
    (hReq : ∀ p, s p O → BafaRequestCode s p) : Nonempty (FixedOrbitRealization s O A) := by
  apply bafa_fixed_orbit_realization base hBAFA hA D.nodes D.edges hReq
  intro p t a r hp hpar x hx
  exact hA t (orbit_graph_parameters_in_transitive hA (hOA p hp) hpar).1 x hx

/-- The orbit, graph, and fixed-part realization are all constructed from an
    actual request in a joint invariant transitive domain. -/
theorem actual_request_fixed_orbit_realization (base : BaseCollection s) (hBAFA : BAFACode s)
    {w B p : U} {J : InternalMask s w → U → U}
    (A : JointMaskDomain s w J B) (hB : TransitiveCode s B)
    (hj : ∀ i, ElementaryMap s s (J i)) (hs : ∀ i x, J i (J i x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hpB : s p B) (hp : BafaRequestCode s p) :
    ∃ O, (∀ q, s q O ↔ ∃ i : InternalMask s w, J i p = q) ∧ s p O ∧
      Nonempty (CodedOrbitDiagram base w J O) ∧ Nonempty (FixedOrbitRealization s O B) := by
  obtain ⟨O, hO, hpO, ⟨D⟩⟩ := actual_request_orbit_diagram base A hB hj hs hOne hMul hpB hp
  have hOB : Subset s O B := by
    intro q hq
    obtain ⟨i, rfl⟩ := (hO q).mp hq
    exact A.stable i p hpB
  have hReq : ∀ q, s q O → BafaRequestCode s q := by
    intro q hq
    obtain ⟨i, rfl⟩ := (hO q).mp hq
    exact (elementary_map_bafa_request (hj i) p).mp hp
  exact ⟨O, hO, hpO, ⟨D⟩, bafa_fixed_orbit_realization_of_bound base hBAFA D hB hOB hReq⟩

#print axioms bafa_fixed_orbit_realization
#print axioms bafa_fixed_orbit_realization_of_bound
end FullBridge
