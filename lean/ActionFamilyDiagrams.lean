import ActionFamilies
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def FamilyDiagramEdge (s : U → U → Prop) (O X Y : U) : Prop :=
  ∃ p t D K x y, s p O ∧ OrbitGraphParameters s p t D K ∧ s x D ∧
    IsOrderedPair s X p x ∧ IsOrderedPair s Y p y ∧ s y x

def familyDiagramEdgeFormula : Formula 3 :=
  .ex (.ex (.ex (.ex (.ex (.ex (.conj (.member 5 8)
    (.conj (orbitGraphParametersFormula 5 4 3 2) (.conj (.member 1 3)
      (.conj (orderedPairFormula 7 5 1) (.conj (orderedPairFormula 6 5 0) (.member 0 1)))))))))))

theorem eval_familyDiagramEdgeFormula (Y X O : U) :
    Eval s familyDiagramEdgeFormula (cons Y (cons X (cons O Fin.elim0))) ↔
      FamilyDiagramEdge s O X Y := by
  simp only [familyDiagramEdgeFormula, Eval, eval_orbitGraphParametersFormula,
    eval_orderedPairFormula, FamilyDiagramEdge]
  rfl

def FamilyDiagramMove (s : U → U → Prop) (O i X Y : U) : Prop :=
  ∃ p t D K x y, s p O ∧ OrbitGraphParameters s p t D K ∧
    IsOrderedPair s X p x ∧ IsOrderedPair s Y p y ∧
      ∃ f, CodedRelation s K i f ∧ CodedRelation s f x y

def familyDiagramMoveFormula : Formula 4 :=
  .ex (.ex (.ex (.ex (.ex (.ex (.conj (.member 5 9)
    (.conj (orbitGraphParametersFormula 5 4 3 2) (.conj (orderedPairFormula 7 5 1)
      (.conj (orderedPairFormula 6 5 0) (jointMaskPointFormula 2 8 1 0))))))))))

theorem eval_familyDiagramMoveFormula (Y X i O : U) :
    Eval s familyDiagramMoveFormula (cons Y (cons X (cons i (cons O Fin.elim0)))) ↔
      FamilyDiagramMove s O i X Y := by
  simp only [familyDiagramMoveFormula, Eval, eval_orbitGraphParametersFormula,
    eval_orderedPairFormula, eval_jointMaskPointFormula, FamilyDiagramMove]
  rfl

theorem action_family_parameters (base : BaseCollection s) {w O p t D K : U}
    (h : ActionFamilyCode base w O) (hp : s p O) (hc : OrbitGraphParameters s p t D K) :
    ∃ Q : CodedMaskAction base w, Q.domain = D ∧ Q.family = K := by
  obtain ⟨Q, y, hy⟩ := h p hp
  have hh := orbit_graph_parameters_unique hy hc
  exact ⟨Q, hh.2.1, hh.2.2⟩

theorem family_diagram_edge_iff (base : BaseCollection s) {w O p x y X Y : U}
    (Q : CodedMaskAction base w) (hp : s p O) (hQ : ActionFamilyMember base p Q)
    (hX : IsOrderedPair s X p x) (hY : IsOrderedPair s Y p y) :
    FamilyDiagramEdge s O X Y ↔ s x Q.domain ∧ s y x := by
  obtain ⟨t, ht⟩ := hQ
  constructor
  · rintro ⟨q, t', D, K, u, v, _, hpar, hu, hXu, hYv, hvu⟩
    obtain ⟨rfl, rfl⟩ := orderedPair_injective hXu hX
    have hvy := (orderedPair_injective hYv hY).2
    subst v
    have hd := (orbit_graph_parameters_unique hpar ht).2.1
    exact ⟨hd ▸ hu, hvu⟩
  · rintro ⟨hx, hy⟩
    exact ⟨p, t, Q.domain, Q.family, x, y, hp, ht, hx, hX, hY, hy⟩

theorem family_diagram_move_iff (base : BaseCollection s) {w O p x y X Y : U}
    (Q : CodedMaskAction base w) (i : InternalMask s w) (hp : s p O)
    (hQ : ActionFamilyMember base p Q) (hX : IsOrderedPair s X p x) (hY : IsOrderedPair s Y p y) :
    FamilyDiagramMove s O i.val X Y ↔ CodedRelation s (Q.maps i) x y := by
  obtain ⟨t, ht⟩ := hQ
  constructor
  · rintro ⟨q, t', D, K, u, v, _, hpar, hXu, hYv, hmove⟩
    obtain ⟨rfl, rfl⟩ := orderedPair_injective hXu hX
    have hvy := (orderedPair_injective hYv hY).2
    subst v
    have hk := (orbit_graph_parameters_unique hpar ht).2.2
    exact (action_family_point_iff base Q i).mp (hk ▸ hmove)
  · intro hxy
    exact ⟨p, t, Q.domain, Q.family, x, y, hp, ht, hX, hY,
      (action_family_point_iff base Q i).mpr hxy⟩

theorem family_diagram_edge_nodes (base : BaseCollection s) {w O X Y : U}
    (h : ActionFamilyCode base w O) (he : FamilyDiagramEdge s O X Y) :
    OrbitDiagramNode s O X ∧ OrbitDiagramNode s O Y := by
  obtain ⟨p, t, D, K, x, y, hp, hpar, hx, hX, hY, hy⟩ := he
  obtain ⟨Q, rfl, rfl⟩ := action_family_parameters base h hp hpar
  exact ⟨⟨p, t, Q.domain, Q.family, x, hp, hpar, hx, hX⟩,
    ⟨p, t, Q.domain, Q.family, y, hp, hpar, Q.transitive x hx y hy, hY⟩⟩

/-- A disjoint tagged membership diagram is an actual internally set-sized graph. -/
theorem action_family_diagram_exists (base : BaseCollection s) {w O : U}
    (h : ActionFamilyCode base w O) :
    ∃ N E, (∀ X, s X N ↔ OrbitDiagramNode s O X) ∧ GraphCode s N E ∧
      (∀ X Y, CodedRelation s E X Y ↔ FamilyDiagramEdge s O X Y) := by
  obtain ⟨T, hT, hOT⟩ := transitive_sets_cover base O
  obtain ⟨P, hP⟩ := base.powerset T
  obtain ⟨PP, hPP⟩ := base.powerset P
  have hb : ∀ X, OrbitDiagramNode s O X → s X PP := by
    rintro X ⟨p, t, D, K, x, hp, hpar, hx, hX⟩
    have hpT := hT O hOT p hp
    have hdT := (orbit_graph_parameters_in_transitive hT hpT hpar).2.1
    exact orderedPair_bound hP hPP hpT (hT D hdT x hx) hX
  obtain ⟨N, hN⟩ := base.separation 1 orbitDiagramNodeFormula (cons O Fin.elim0) PP
  have hn : ∀ X, s X N ↔ OrbitDiagramNode s O X := by
    intro X
    rw [hN, eval_orbitDiagramNodeFormula]
    exact ⟨fun h => h.2, fun h => ⟨hb X h, h⟩⟩
  obtain ⟨E, hE, he⟩ := normalized_relation_comprehension base familyDiagramEdgeFormula (cons O Fin.elim0) N
  refine ⟨N, E, hn, hE, fun X Y => ?_⟩
  rw [he, eval_familyDiagramEdgeFormula]
  exact ⟨fun h => h.2.2, fun e => ⟨(hn X).mpr (family_diagram_edge_nodes base h e).1,
    (hn Y).mpr (family_diagram_edge_nodes base h e).2, e⟩⟩

#print axioms action_family_diagram_exists
end FullBridge
