import JointActionFamilyDiagrams
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def FamilyBoundaryValue (s : U → U → Prop) (O A X x : U) : Prop :=
  ∃ p t D K, s p O ∧ OrbitGraphParameters s p t D K ∧ s x A ∧ IsOrderedPair s X p x

def familyBoundaryValueFormula : Formula 4 :=
  .ex (.ex (.ex (.ex (.conj (.member 3 6) (.conj (orbitGraphParametersFormula 3 2 1 0)
    (.conj (.member 4 7) (orderedPairFormula 5 3 4)))))))

theorem eval_familyBoundaryValueFormula (O A X x : U) :
    Eval s familyBoundaryValueFormula (cons x (cons X (cons O (cons A Fin.elim0)))) ↔
      FamilyBoundaryValue s O A X x := by
  simp only [familyBoundaryValueFormula, Eval, eval_orbitGraphParametersFormula,
    eval_orderedPairFormula, FamilyBoundaryValue]
  rfl

theorem family_boundary_value_unique {O A X x y : U}
    (hx : FamilyBoundaryValue s O A X x) (hy : FamilyBoundaryValue s O A X y) : x = y := by
  obtain ⟨_, _, _, _, _, _, _, hx⟩ := hx
  obtain ⟨_, _, _, _, _, _, _, hy⟩ := hy
  exact (orderedPair_injective hx hy).2

theorem family_boundary_node (base : BaseCollection s) {w O X x : U}
    (P : CodedMaskAction base w) (h : ActionFamilyCode base w O)
    (he : ∀ p Q, s p O → ActionFamilyMember base p Q → CodedMaskExtends base P Q)
    (hx : FamilyBoundaryValue s O P.domain X x) : OrbitDiagramNode s O X := by
  obtain ⟨p, t, D, K, hp, hpar, hx, hX⟩ := hx
  obtain ⟨Q, rfl, rfl⟩ := action_family_parameters base h hp hpar
  exact ⟨p, t, Q.domain, Q.family, x, hp, hpar, (he p Q hp ⟨t, hpar⟩).1 x hx, hX⟩

structure ActionFamilyBoundary (s : U → U → Prop) (O A N E : U) where
  domain : U
  code : U
  members : ∀ X, s X domain ↔ ∃ x, FamilyBoundaryValue s O A X x
  values : ∀ X x, CodedRelation s code X x ↔ FamilyBoundaryValue s O A X x
  closed : GraphClosedCode s N E domain
  decoration : DecorationCode s domain E code

theorem action_family_boundary_exists (base : BaseCollection s) {w O N E : U}
    (P : CodedMaskAction base w) (h : ActionFamilyCode base w O)
    (he : ∀ p Q, s p O → ActionFamilyMember base p Q → CodedMaskExtends base P Q)
    (hN : ∀ X, s X N ↔ OrbitDiagramNode s O X)
    (hE : ∀ X Y, CodedRelation s E X Y ↔ FamilyDiagramEdge s O X Y) :
    Nonempty (ActionFamilyBoundary s O P.domain N E) := by
  obtain ⟨D, hD⟩ := base.separation 2 (.ex familyBoundaryValueFormula)
    (cons O (cons P.domain Fin.elim0)) N
  have hd : ∀ X, s X D ↔ ∃ x, FamilyBoundaryValue s O P.domain X x := by
    intro X
    have hh : s X D ↔ s X N ∧ ∃ x, FamilyBoundaryValue s O P.domain X x := by
      simpa only [Eval, eval_familyBoundaryValueFormula] using hD X
    exact hh.trans ⟨fun h => h.2, fun ⟨x, hx⟩ =>
      ⟨(hN X).mpr (family_boundary_node base P h he hx), x, hx⟩⟩
  obtain ⟨b, hb, hbr⟩ := definable_function_code base familyBoundaryValueFormula
    (cons O (cons P.domain Fin.elim0)) D (by
      intro X hX
      obtain ⟨x, hx⟩ := (hd X).mp hX
      exact ⟨x, (eval_familyBoundaryValueFormula O P.domain X x).mpr hx,
        fun y hy => family_boundary_value_unique ((eval_familyBoundaryValueFormula O P.domain X y).mp hy) hx⟩)
  have hv : ∀ X x, CodedRelation s b X x ↔ FamilyBoundaryValue s O P.domain X x := by
    intro X x
    rw [hbr, eval_familyBoundaryValueFormula]
    exact ⟨fun h => h.2, fun h => ⟨(hd X).mpr ⟨x, h⟩, h⟩⟩
  have hchild : ∀ X x Y, FamilyBoundaryValue s O P.domain X x → CodedRelation s E X Y →
      ∃ y, FamilyBoundaryValue s O P.domain Y y ∧ s y x := by
    intro X x Y hx hXY
    obtain ⟨p, t, a, K, hp, hpar, hx, hX⟩ := hx
    obtain ⟨Q, rfl, rfl⟩ := action_family_parameters base h hp hpar
    obtain ⟨y, hY, _, hyx⟩ := (family_diagram_edge_from base Q hp ⟨t, hpar⟩ hX).mp ((hE X Y).mp hXY)
    exact ⟨y, ⟨p, t, Q.domain, Q.family, hp, hpar, P.transitive x hx y hyx, hY⟩, hyx⟩
  have hc : GraphClosedCode s N E D := by
    refine ⟨fun X hX => ?_, ?_⟩
    · obtain ⟨x, hx⟩ := (hd X).mp hX
      exact (hN X).mpr (family_boundary_node base P h he hx)
    · intro X hX Y hXY
      obtain ⟨x, hx⟩ := (hd X).mp hX
      obtain ⟨y, hy, _⟩ := hchild X x Y hx hXY
      exact (hd Y).mpr ⟨y, hy⟩
  refine ⟨⟨D, b, hd, hv, hc, hb, ?_⟩⟩
  intro X _ x hXx y
  constructor
  · intro hyx
    obtain ⟨p, t, a, K, hp, hpar, hx, hX⟩ := (hv X x).mp hXx
    obtain ⟨Q, rfl, rfl⟩ := action_family_parameters base h hp hpar
    obtain ⟨Y, hY⟩ := orderedPair_exists base.pairing p y
    have hyb : FamilyBoundaryValue s O P.domain Y y :=
      ⟨p, t, Q.domain, Q.family, hp, hpar, P.transitive x hx y hyx, hY⟩
    exact ⟨Y, (hd Y).mpr ⟨y, hyb⟩, (hE X Y).mpr
      ((family_diagram_edge_iff base Q hp ⟨t, hpar⟩ hX hY).mpr
        ⟨(he p Q hp ⟨t, hpar⟩).1 x hx, hyx⟩), (hv Y y).mpr hyb⟩
  · rintro ⟨Y, _, hXY, hYy⟩
    obtain ⟨z, hz, hzx⟩ := hchild X x Y ((hv X x).mp hXx) hXY
    exact (family_boundary_value_unique hz ((hv Y y).mp hYy)) ▸ hzx

theorem action_family_boundary_old {O A N E : U} (B : ActionFamilyBoundary s O A N E) :
    ∀ X x, CodedRelation s B.code X x → s x A := by
  intro X x h
  obtain ⟨_, _, _, _, _, _, hx, _⟩ := (B.values X x).mp h
  exact hx

theorem action_family_boundary_compatible (base : BaseCollection s) {w O N E : U}
    (P : CodedMaskAction base w) (h : ActionFamilyCode base w O)
    (he : ∀ p Q, s p O → ActionFamilyMember base p Q → CodedMaskExtends base P Q)
    (B : ActionFamilyBoundary s O P.domain N E) (G : CodedMaskGraphAction base P N E)
    (hG : ∀ i X Y, CodedRelation s (G.maps i) X Y ↔ FamilyDiagramMove s O i.val X Y) :
    ∀ i, BoundaryActionCompatible s B.code (P.maps i) (G.maps i) := by
  intro i X Y x y hXY hXx hxy
  obtain ⟨p, t, D, K, hp, hpar, hx, hX⟩ := (B.values X x).mp hXx
  obtain ⟨Q, rfl, rfl⟩ := action_family_parameters base h hp hpar
  obtain ⟨z, hY, hxz⟩ := (family_diagram_move_from base Q i hp ⟨t, hpar⟩ hX).mp ((hG i X Y).mp hXY)
  have hzy := coded_function_value_unique (Q.iso i).1 hxz ((he p Q hp ⟨t, hpar⟩).2 i x y hxy)
  exact (B.values Y y).mpr ⟨p, t, Q.domain, Q.family, hp, hpar,
    ((P.iso i).2.2.1 y).mpr ⟨x, hx, hxy⟩, hzy ▸ hY⟩

#print axioms action_family_boundary_exists
#print axioms action_family_boundary_compatible
end FullBridge
