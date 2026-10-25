import OrbitDiagramComponents
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem joint_domain_graph_actions (base : BaseCollection s) {w N E : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J N)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hEdge : ∀ i x y, CodedRelation s E x y → CodedRelation s E (J i x) (J i y)) :
    ∃ maps : InternalMask s w → U,
      (∀ i, CodedRelation s A.family i.val (maps i)) ∧
      (∀ i, GraphIsoCode s N E N E (maps i)) ∧
      (∀ x y, CodedRelation s (maps (internalMaskOne base w)) x y → x = y) ∧
      (∀ i j x z, CodedRelation s (maps (internalMaskMul base i j)) x z ↔
        ∃ y, CodedRelation s (maps j) x y ∧ CodedRelation s (maps i) y z) := by
  classical
  let maps := fun i => Classical.choose (joint_mask_graph_exists A i)
  have hspec := fun i => Classical.choose_spec (joint_mask_graph_exists A i)
  have hf := fun i => (hspec i).2.1
  have hr := fun i => (hspec i).2.2
  have ht : ∀ i x y, CodedRelation s (maps i) x y → s y N := by
    intro i x y hxy
    obtain ⟨hx, hy⟩ := (hr i x y).mp hxy
    exact hy ▸ A.stable i x hx
  have hone : ∀ x y, CodedRelation s (maps (internalMaskOne base w)) x y → x = y := by
    intro x y hxy
    exact (hOne x).symm.trans ((hr _ x y).mp hxy).2
  have hmul : ∀ i j x z, CodedRelation s (maps (internalMaskMul base i j)) x z ↔
      ∃ y, CodedRelation s (maps j) x y ∧ CodedRelation s (maps i) y z := by
    intro i j x z
    constructor
    · intro hxz
      obtain ⟨hx, hz⟩ := (hr _ x z).mp hxz
      exact ⟨J j x, (hr j x _).mpr ⟨hx, rfl⟩,
        (hr i _ z).mpr ⟨A.stable j x hx, (hMul i j x).symm.trans hz⟩⟩
    · rintro ⟨y, hxy, hyz⟩
      obtain ⟨hx, hy⟩ := (hr j x y).mp hxy
      obtain ⟨_, hz⟩ := (hr i y z).mp hyz
      exact (hr _ x z).mpr ⟨hx, (hMul i j x).trans ((congrArg (J i) hy).trans hz)⟩
  have hEdges : ∀ i x y X Y, CodedRelation s (maps i) x X → CodedRelation s (maps i) y Y →
      CodedRelation s E x y → CodedRelation s E X Y := by
    intro i x y X Y hx hy hxy
    exact ((hr i x X).mp hx).2 ▸ ((hr i y Y).mp hy).2 ▸ hEdge i x y hxy
  exact ⟨maps, fun i => (hspec i).1,
    coded_group_graph_isomorphisms (internalMaskGroup base w) maps hf ht hone hmul hEdges, hone, hmul⟩

structure CodedOrbitDiagram (base : BaseCollection s) (w : U)
    (J : InternalMask s w → U → U) (O : U) where
  domain : U
  edge : U
  nodes : ∀ X, s X domain ↔ OrbitDiagramNode s O X
  graph : GraphCode s domain edge
  edges : ∀ X Y, CodedRelation s edge X Y ↔ OrbitDiagramEdge s O X Y
  joint : JointMaskDomain s w J domain
  maps : InternalMask s w → U
  mapCodes : ∀ i, CodedRelation s joint.family i.val (maps i)
  iso : ∀ i, GraphIsoCode s domain edge domain edge (maps i)
  one : ∀ x y, CodedRelation s (maps (internalMaskOne base w)) x y → x = y
  mul : ∀ i j x z, CodedRelation s (maps (internalMaskMul base i j)) x z ↔
    ∃ y, CodedRelation s (maps j) x y ∧ CodedRelation s (maps i) y z
  components : ∀ p t a r, s p O → OrbitGraphParameters s p t a r →
    Nonempty (OrbitDiagramComponent s domain edge p a r)

theorem coded_orbit_diagram_exists (base : BaseCollection s) {w B O : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J B) (hB : TransitiveCode s B)
    (hj : ∀ i, ElementaryMap s s (J i)) (hs : ∀ i x, J i (J i x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hOB : Subset s O B) (hReq : ∀ p, s p O → BafaRequestCode s p)
    (hO : ∀ i p, s p O → s (J i p) O) : Nonempty (CodedOrbitDiagram base w J O) := by
  obtain ⟨pB, ppB, N, E, hpB, hppB, hN, hBound, hG, hE⟩ := orbit_diagram_codes_exist base hB hOB hReq
  obtain ⟨A1⟩ := joint_mask_domain_powerset base A hj hs hpB
  obtain ⟨A2⟩ := joint_mask_domain_powerset base A1 hj hs hppB
  have hStable : ∀ i X, s X N → s (J i X) N := fun i X hX =>
    (hN _).mpr (orbit_diagram_node_map (hj i) (hO i) ((hN X).mp hX))
  obtain ⟨Q⟩ := joint_mask_domain_restrict base A2 hBound hStable
  have hEdges : ∀ i X Y, CodedRelation s E X Y → CodedRelation s E (J i X) (J i Y) := fun i X Y hXY =>
    (hE _ _).mpr (orbit_diagram_edge_map (hj i) (hO i) ((hE X Y).mp hXY))
  obtain ⟨maps, hcodes, hiso, hone, hmul⟩ := joint_domain_graph_actions base Q hOne hMul hEdges
  exact ⟨⟨N, E, hN, hG, hE, Q, maps, hcodes, hiso, hone, hmul,
    fun p t a r hp hpar => orbit_diagram_component_exists base hN hE hp hpar (hReq p hp)⟩⟩

theorem actual_request_orbit_diagram (base : BaseCollection s) {w B p : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J B) (hB : TransitiveCode s B)
    (hj : ∀ i, ElementaryMap s s (J i)) (hs : ∀ i x, J i (J i x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hpB : s p B) (hReq : BafaRequestCode s p) :
    ∃ O, (∀ q, s q O ↔ ∃ i : InternalMask s w, J i p = q) ∧ s p O ∧
      Nonempty (CodedOrbitDiagram base w J O) := by
  obtain ⟨_, O, _, _, hOm, hOB, _⟩ := joint_mask_orbit_exists base A hpB hMul
  have hO : ∀ i q, s q O → s (J i q) O := by
    intro i q hq
    obtain ⟨j, rfl⟩ := (hOm q).mp hq
    exact (hOm _).mpr ⟨internalMaskMul base i j, hMul i j p⟩
  have hAllReq : ∀ q, s q O → BafaRequestCode s q := by
    intro q hq
    obtain ⟨i, rfl⟩ := (hOm q).mp hq
    exact (elementary_map_bafa_request (hj i) p).mp hReq
  exact ⟨O, hOm, (hOm p).mpr ⟨internalMaskOne base w, hOne p⟩,
    coded_orbit_diagram_exists base A hB hj hs hOne hMul hOB hAllReq hO⟩

#print axioms coded_orbit_diagram_exists
#print axioms actual_request_orbit_diagram
end FullBridge
