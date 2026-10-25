import OrbitComponentSolutions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- All boundary copies with value x must be identified with the literal old x. -/
def OrbitBoundaryValue (s : U → U → Prop) (O X x : U) : Prop :=
  ∃ p t a r, s p O ∧ OrbitGraphParameters s p t a r ∧ s x t ∧ IsOrderedPair s X p x

def orbitBoundaryValueFormula : Formula 3 :=
  .ex (.ex (.ex (.ex (.conj (.member 3 6) (.conj (orbitGraphParametersFormula 3 2 1 0)
    (.conj (.member 4 2) (orderedPairFormula 5 3 4)))))))

theorem eval_orbitBoundaryValueFormula (O X x : U) :
    Eval s orbitBoundaryValueFormula (cons x (cons X (cons O Fin.elim0))) ↔ OrbitBoundaryValue s O X x := by
  simp only [orbitBoundaryValueFormula, Eval, eval_orbitGraphParametersFormula,
    eval_orderedPairFormula, OrbitBoundaryValue]
  rfl

theorem orbit_boundary_value_unique {O X x y : U}
    (hx : OrbitBoundaryValue s O X x) (hy : OrbitBoundaryValue s O X y) : x = y := by
  obtain ⟨_, _, _, _, _, _, _, hp⟩ := hx
  obtain ⟨_, _, _, _, _, _, _, hq⟩ := hy
  exact (orderedPair_injective hp hq).2

theorem orbit_boundary_node {O X x : U} (hReq : ∀ p, s p O → BafaRequestCode s p)
    (hx : OrbitBoundaryValue s O X x) : OrbitDiagramNode s O X := by
  obtain ⟨p, t, a, r, hp, hpar, hx, hX⟩ := hx
  exact ⟨p, t, a, r, x, hp, hpar, (bafa_request_parameters (hReq p hp) hpar).2.2.2.1 x hx, hX⟩

theorem orbit_boundary_codes_exist (base : BaseCollection s) {O N : U}
    (hN : ∀ X, s X N ↔ OrbitDiagramNode s O X)
    (hReq : ∀ p, s p O → BafaRequestCode s p) :
    ∃ D b, Subset s D N ∧ (∀ X, s X D ↔ ∃ x, OrbitBoundaryValue s O X x) ∧
      FunctionCode s D b ∧ ∀ X x, CodedRelation s b X x ↔ OrbitBoundaryValue s O X x := by
  obtain ⟨D, hD⟩ := base.separation 1 (.ex orbitBoundaryValueFormula) (cons O Fin.elim0) N
  have hDm : ∀ X, s X D ↔ ∃ x, OrbitBoundaryValue s O X x := by
    intro X
    have h : s X D ↔ s X N ∧ ∃ x, OrbitBoundaryValue s O X x := by
      simpa only [Eval, eval_orbitBoundaryValueFormula] using hD X
    exact h.trans ⟨fun hx => hx.2, fun ⟨x, hx⟩ => ⟨(hN X).mpr (orbit_boundary_node hReq hx), x, hx⟩⟩
  obtain ⟨b, hb, hbr⟩ := definable_function_code base orbitBoundaryValueFormula (cons O Fin.elim0) D (by
    intro X hX
    obtain ⟨x, hx⟩ := (hDm X).mp hX
    exact ⟨x, (eval_orbitBoundaryValueFormula O X x).mpr hx,
      fun y hy => orbit_boundary_value_unique ((eval_orbitBoundaryValueFormula O X y).mp hy) hx⟩)
  refine ⟨D, b, fun X hX => (hN X).mpr (by
    obtain ⟨x, hx⟩ := (hDm X).mp hX
    exact orbit_boundary_node hReq hx), hDm, hb, fun X x => ?_⟩
  rw [hbr, eval_orbitBoundaryValueFormula]
  exact ⟨fun h => h.2, fun h => ⟨(hDm X).mpr ⟨x, h⟩, h⟩⟩

theorem orbit_boundary_value_map {j : U → U} (hj : ElementaryMap s s j) {O X x : U}
    (hO : ∀ p, s p O → s (j p) O) (hx : OrbitBoundaryValue s O X x) :
    OrbitBoundaryValue s O (j X) (j x) := by
  obtain ⟨p, t, a, r, hp, hpar, hx, hX⟩ := hx
  have hxt : s (j x) (j t) := (hj (Formula.member (n := 2) 0 1) (cons x (cons t Fin.elim0))).mp hx
  exact ⟨j p, j t, j a, j r, hO p hp, elementary_map_graph_parameters hj hpar,
    hxt, elementary_map_ordered_pair hj hX⟩

structure OrbitBoundary (s : U → U → Prop) (O N E : U) where
  domain : U
  code : U
  members : ∀ X, s X domain ↔ ∃ x, OrbitBoundaryValue s O X x
  values : ∀ X x, CodedRelation s code X x ↔ OrbitBoundaryValue s O X x
  closed : GraphClosedCode s N E domain
  decoration : DecorationCode s domain E code

theorem orbit_boundary_exists (base : BaseCollection s) {O N E : U}
    (hN : ∀ X, s X N ↔ OrbitDiagramNode s O X)
    (hE : ∀ X Y, CodedRelation s E X Y ↔ OrbitDiagramEdge s O X Y)
    (hReq : ∀ p, s p O → BafaRequestCode s p) : Nonempty (OrbitBoundary s O N E) := by
  obtain ⟨D, b, hDN, hD, hb, hbr⟩ := orbit_boundary_codes_exist base hN hReq
  have hchild : ∀ X x Y, OrbitBoundaryValue s O X x → CodedRelation s E X Y →
      ∃ y, OrbitBoundaryValue s O Y y ∧ s y x := by
    intro X x Y hX hXY
    obtain ⟨p, t, a, r, hp, hpar, hx, hpair⟩ := hX
    obtain ⟨q, t', a', r', u, v, _, hpar', hXu, hYv, huv⟩ := (hE X Y).mp hXY
    obtain ⟨hqp, hux⟩ := orderedPair_injective hXu hpair
    subst q
    subst u
    obtain ⟨htt, haa, hrr⟩ := orbit_graph_parameters_unique hpar' hpar
    subst t'
    subst a'
    subst r'
    have hReqp := bafa_request_parameters (hReq p hp) hpar
    have hvx := (hReqp.2.2.2.2 x hx v).mp huv
    exact ⟨v, ⟨p, t, a, r, hp, hpar, hReqp.1 x hx v hvx, hYv⟩, hvx⟩
  have hclosed : GraphClosedCode s N E D := by
    refine ⟨hDN, ?_⟩
    intro X hX Y hXY
    obtain ⟨x, hx⟩ := (hD X).mp hX
    obtain ⟨y, hy, _⟩ := hchild X x Y hx hXY
    exact (hD Y).mpr ⟨y, hy⟩
  refine ⟨⟨D, b, hD, hbr, hclosed, hb, ?_⟩⟩
  intro X _ x hXx y
  constructor
  · intro hyx
    obtain ⟨p, t, a, r, hp, hpar, hx, hpair⟩ := (hbr X x).mp hXx
    have hReqp := bafa_request_parameters (hReq p hp) hpar
    obtain ⟨Y, hY⟩ := orderedPair_exists base.pairing p y
    have hboundary : OrbitBoundaryValue s O Y y :=
      ⟨p, t, a, r, hp, hpar, hReqp.1 x hx y hyx, hY⟩
    exact ⟨Y, (hD Y).mpr ⟨y, hboundary⟩,
      (hE X Y).mpr ⟨p, t, a, r, x, y, hp, hpar, hpair, hY,
        (hReqp.2.2.2.2 x hx y).mpr hyx⟩, (hbr Y y).mpr hboundary⟩
  · rintro ⟨Y, _, hXY, hYy⟩
    obtain ⟨v, hv, hvx⟩ := hchild X x Y ((hbr X x).mp hXx) hXY
    exact orbit_boundary_value_unique hv ((hbr Y y).mp hYy) ▸ hvx

theorem orbit_boundary_on_component {O N E p t a r x X : U}
    (B : OrbitBoundary s O N E) (C : OrbitDiagramComponent s N E p a r)
    (hp : s p O) (hpar : OrbitGraphParameters s p t a r)
    (hxX : CodedRelation s C.code x X) :
    (s X B.domain ↔ s x t) ∧ (s x t → CodedRelation s B.code X x) := by
  have hpair := ((C.values x X).mp hxX).2
  have hb : s x t → OrbitBoundaryValue s O X x :=
    fun hx => ⟨p, t, a, r, hp, hpar, hx, hpair⟩
  refine ⟨⟨?_, fun hx => (B.members X).mpr ⟨x, hb hx⟩⟩, fun hx => (B.values X x).mpr (hb hx)⟩
  intro hX
  obtain ⟨y, q, t', a', r', _, hpar', hy, hpair'⟩ := (B.members X).mp hX
  obtain ⟨hqp, hyx⟩ := orderedPair_injective hpair' hpair
  subst q
  subst y
  exact (orbit_graph_parameters_unique hpar' hpar).1 ▸ hy

theorem orbit_boundary_values_in_old {O N E A : U} (B : OrbitBoundary s O N E)
    (hOld : ∀ p t a r, s p O → OrbitGraphParameters s p t a r → Subset s t A) :
    ∀ X x, CodedRelation s B.code X x → s x A := by
  intro X x hXx
  obtain ⟨p, t, a, r, hp, hpar, hx, _⟩ := (B.values X x).mp hXx
  exact hOld p t a r hp hpar x hx

theorem orbit_boundary_equivariant {j : U → U} (hj : ElementaryMap s s j) {O N E : U}
    (B : OrbitBoundary s O N E) (hO : ∀ p, s p O → s (j p) O) :
    ∀ X x, CodedRelation s B.code X x → CodedRelation s B.code (j X) (j x) := by
  intro X x hXx
  exact (B.values (j X) (j x)).mpr (orbit_boundary_value_map hj hO ((B.values X x).mp hXx))

#print axioms orbit_boundary_exists
end FullBridge
