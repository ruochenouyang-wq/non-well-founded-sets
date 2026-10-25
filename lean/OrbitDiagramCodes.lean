import OrbitGraphParameters
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def OrbitDiagramNode (s : U → U → Prop) (O Z : U) : Prop :=
  ∃ p t a r x, s p O ∧ OrbitGraphParameters s p t a r ∧ s x a ∧ IsOrderedPair s Z p x

def orbitDiagramNodeFormula : Formula 2 :=
  .ex (.ex (.ex (.ex (.ex (.conj (.member 4 6)
    (.conj (orbitGraphParametersFormula 4 3 2 1)
      (.conj (.member 0 2) (orderedPairFormula 5 4 0))))))))

theorem eval_orbitDiagramNodeFormula (Z O : U) :
    Eval s orbitDiagramNodeFormula (cons Z (cons O Fin.elim0)) ↔ OrbitDiagramNode s O Z := by
  simp only [orbitDiagramNodeFormula, Eval, eval_orbitGraphParametersFormula, eval_orderedPairFormula, OrbitDiagramNode]
  rfl

def OrbitDiagramEdge (s : U → U → Prop) (O X Y : U) : Prop :=
  ∃ p t a r x y, s p O ∧ OrbitGraphParameters s p t a r ∧
    IsOrderedPair s X p x ∧ IsOrderedPair s Y p y ∧ CodedRelation s r x y

def orbitDiagramEdgeFormula : Formula 3 :=
  .ex (.ex (.ex (.ex (.ex (.ex (.conj (.member 5 8)
    (.conj (orbitGraphParametersFormula 5 4 3 2) (.conj (orderedPairFormula 7 5 1)
      (.conj (orderedPairFormula 6 5 0) (relatedFormula 2 1 0))))))))))

theorem eval_orbitDiagramEdgeFormula (Y X O : U) :
    Eval s orbitDiagramEdgeFormula (cons Y (cons X (cons O Fin.elim0))) ↔ OrbitDiagramEdge s O X Y := by
  simp only [orbitDiagramEdgeFormula, Eval, eval_orbitGraphParametersFormula, eval_orderedPairFormula,
    eval_relatedFormula, OrbitDiagramEdge]
  rfl

theorem orbit_diagram_edge_nodes {O X Y : U} (hReq : ∀ p, s p O → BafaRequestCode s p)
    (h : OrbitDiagramEdge s O X Y) : OrbitDiagramNode s O X ∧ OrbitDiagramNode s O Y := by
  obtain ⟨p, t, a, r, x, y, hp, hpar, hX, hY, hxy⟩ := h
  have hG := (bafa_request_parameters (hReq p hp) hpar).2.1
  have hends := graphCode_endpoints hG hxy
  exact ⟨⟨p, t, a, r, x, hp, hpar, hends.1, hX⟩,
    ⟨p, t, a, r, y, hp, hpar, hends.2, hY⟩⟩

/-- Actual source comprehension, bounded by two powersets of a transitive
    joint domain; no external collection of orbit nodes is substituted. -/
theorem orbit_diagram_codes_exist (base : BaseCollection s) {B O : U}
    (hB : TransitiveCode s B) (hOB : Subset s O B) (hReq : ∀ p, s p O → BafaRequestCode s p) :
    ∃ pB ppB N E,
      (∀ x, s x pB ↔ Subset s x B) ∧ (∀ x, s x ppB ↔ Subset s x pB) ∧
      (∀ X, s X N ↔ OrbitDiagramNode s O X) ∧ Subset s N ppB ∧
      GraphCode s N E ∧ (∀ X Y, CodedRelation s E X Y ↔ OrbitDiagramEdge s O X Y) := by
  obtain ⟨pB, hpB⟩ := base.powerset B
  obtain ⟨ppB, hppB⟩ := base.powerset pB
  have hbound : ∀ X, OrbitDiagramNode s O X → s X ppB := by
    rintro X ⟨p, t, a, r, x, hp, hpar, hx, hX⟩
    have hpB' := hOB p hp
    have haB := (orbit_graph_parameters_in_transitive hB hpB' hpar).2.1
    exact orderedPair_bound hpB hppB hpB' (hB a haB x hx) hX
  obtain ⟨N, hN⟩ := base.separation 1 orbitDiagramNodeFormula (cons O Fin.elim0) ppB
  have hNm : ∀ X, s X N ↔ OrbitDiagramNode s O X := by
    intro X
    rw [hN, eval_orbitDiagramNodeFormula]
    exact ⟨fun h => h.2, fun h => ⟨hbound X h, h⟩⟩
  obtain ⟨E, hE, hEr⟩ := normalized_relation_comprehension base orbitDiagramEdgeFormula (cons O Fin.elim0) N
  refine ⟨pB, ppB, N, E, hpB, hppB, hNm, fun X hX => hbound X ((hNm X).mp hX), hE, ?_⟩
  intro X Y
  rw [hEr, eval_orbitDiagramEdgeFormula]
  exact ⟨fun h => h.2.2, fun h => ⟨(hNm X).mpr (orbit_diagram_edge_nodes hReq h).1,
    (hNm Y).mpr (orbit_diagram_edge_nodes hReq h).2, h⟩⟩

theorem orbit_diagram_node_map {j : U → U} (hj : ElementaryMap s s j) {O X : U}
    (hO : ∀ p, s p O → s (j p) O) (hX : OrbitDiagramNode s O X) : OrbitDiagramNode s O (j X) := by
  obtain ⟨p, t, a, r, x, hp, hpar, hx, hpair⟩ := hX
  have hxa : s (j x) (j a) := (hj (Formula.member (n := 2) 0 1) (cons x (cons a Fin.elim0))).mp hx
  exact ⟨j p, j t, j a, j r, j x, hO p hp, elementary_map_graph_parameters hj hpar,
    hxa, elementary_map_ordered_pair hj hpair⟩

theorem orbit_diagram_edge_map {j : U → U} (hj : ElementaryMap s s j) {O X Y : U}
    (hO : ∀ p, s p O → s (j p) O) (hXY : OrbitDiagramEdge s O X Y) : OrbitDiagramEdge s O (j X) (j Y) := by
  obtain ⟨p, t, a, r, x, y, hp, hpar, hX, hY, hxy⟩ := hXY
  exact ⟨j p, j t, j a, j r, j x, j y, hO p hp, elementary_map_graph_parameters hj hpar,
    elementary_map_ordered_pair hj hX, elementary_map_ordered_pair hj hY,
    (elementary_map_coded_relation hj r x y).mp hxy⟩

#print axioms orbit_diagram_codes_exist
end FullBridge
