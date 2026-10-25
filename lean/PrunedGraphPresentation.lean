import TaggedGraphSolutions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Actual source-set-sized presentation of the members of one target set. -/
structure PrunedNodePresentation (base : BaseCollection s) (b : U) (A : PrunedQuotient base b) where
  representatives : U
  clean : ∀ x, s x representatives → ¬s b x
  image : prunedCode base b representatives = A
  relation : U
  relation_iff : ∀ x y, CodedRelation s relation x y ↔
    s x representatives ∧ s y representatives ∧ prunedCode base b x = prunedCode base b y
  nodes : U
  nodes_iff : ∀ c, s c nodes ↔ ∃ x, s x representatives ∧ GraphClassCode s representatives relation x c

theorem pruned_node_presentation_exists (base : BaseCollection s) {b : U} (hbb : s b b)
    (A : PrunedQuotient base b) : Nonempty (PrunedNodePresentation base b A) := by
  obtain ⟨a, ha, hq⟩ := pruned_clean_representative base hbb A
  obtain ⟨m, _, hm⟩ := normalized_relation_comprehension base (globalLeastFormula prunedMemberFormula)
    (cons b Fin.elim0) a
  have hm' : ∀ x y, CodedRelation s m x y ↔
      s x a ∧ s y a ∧ prunedCode base b x = prunedCode base b y := by
    intro x y
    exact (hm x y).trans (and_congr_right (fun _ => and_congr_right (fun _ =>
      (eval_globalLeastFormula prunedMemberFormula (cons b Fin.elim0) x y).trans
        (least_global_code_eq base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b) x y).symm)))
  obtain ⟨C, hC⟩ := graph_class_nodes_exists base a m
  exact ⟨⟨a, ha, hq, m, hm', C, hC⟩⟩

def PrunedNodeCorresponds {base : BaseCollection s} {b : U} {A : PrunedQuotient base b}
    (P : PrunedNodePresentation base b A) (c : U) (X : PrunedQuotient base b) : Prop :=
  ∃ x, s x P.representatives ∧ GraphClassCode s P.representatives P.relation x c ∧ prunedCode base b x = X

theorem pruned_node_class_eq (base : BaseCollection s) {b : U} {A : PrunedQuotient base b}
    (P : PrunedNodePresentation base b A) {x y c d : U}
    (hx : s x P.representatives) (hy : s y P.representatives)
    (hc : GraphClassCode s P.representatives P.relation x c)
    (hd : GraphClassCode s P.representatives P.relation y d) :
    c = d ↔ prunedCode base b x = prunedCode base b y := by
  constructor
  · intro hcd
    have hxc := (hc x).mpr ⟨hx, (P.relation_iff x x).mpr ⟨hx, hx, rfl⟩⟩
    have hxd : s x d := hcd ▸ hxc
    exact ((P.relation_iff y x).mp ((hd x).mp hxd).2).2.2.symm
  · intro hxy
    apply base.extensional
    intro z
    rw [hc z, hd z, P.relation_iff x z, P.relation_iff y z]
    exact ⟨fun h => ⟨h.1, hy, h.1, hxy.symm.trans h.2.2.2⟩,
      fun h => ⟨h.1, hx, h.1, hxy.trans h.2.2.2⟩⟩

theorem pruned_node_correspondence_eq (base : BaseCollection s) {b : U} {A : PrunedQuotient base b}
    (P : PrunedNodePresentation base b A) {c d : U} {X Y : PrunedQuotient base b}
    (hc : PrunedNodeCorresponds P c X) (hd : PrunedNodeCorresponds P d Y) : c = d ↔ X = Y := by
  obtain ⟨x, hx, hxc, rfl⟩ := hc
  obtain ⟨y, hy, hyd, rfl⟩ := hd
  exact pruned_node_class_eq base P hx hy hxc hyd

theorem pruned_node_correspondence_total (base : BaseCollection s) {b : U} (hbb : s b b)
    {A : PrunedQuotient base b} (P : PrunedNodePresentation base b A) :
    (∀ c, s c P.nodes → ∃ X, prunedMember base b X A ∧ PrunedNodeCorresponds P c X) ∧
    (∀ X, prunedMember base b X A → ∃ c, s c P.nodes ∧ PrunedNodeCorresponds P c X) := by
  have hrow : ∀ X, prunedMember base b X A ↔ ∃ x, s x P.representatives ∧ prunedCode base b x = X := by
    intro X
    have h := (pruned_good_row base hbb P.clean).2 X
    simpa only [P.image] using h
  constructor
  · intro c hc
    obtain ⟨x, hx, hxc⟩ := (P.nodes_iff c).mp hc
    exact ⟨prunedCode base b x, (hrow _).mpr ⟨x, hx, rfl⟩, x, hx, hxc, rfl⟩
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := (hrow X).mp hX
    obtain ⟨c, hc⟩ := graph_class_exists base P.representatives P.relation x
    exact ⟨c, (P.nodes_iff c).mpr ⟨x, hx, hc⟩, x, hx, hc, rfl⟩

def prunedRelatedFormula {n} (b r x y : Fin n) : Formula n :=
  Formula.translateParameters (leastGlobalEqualFormula prunedMemberFormula)
    (leastGlobalMemberFormula prunedMemberFormula) (fun _ => b) id (relatedFormula r x y)

theorem eval_prunedRelatedFormula (base : BaseCollection s) {n} (b r x y : Fin n) (e : Fin n → U) :
    Eval s (prunedRelatedFormula b r x y) e ↔
      CodedRelation (prunedMember base (e b)) (prunedCode base (e b) (e r))
        (prunedCode base (e b) (e x)) (prunedCode base (e b) (e y)) := by
  have h := least_global_formula_translation base prunedMemberFormula (cons (e b) Fin.elim0)
    (pruned_edges_are_members (e b)) (relatedFormula r x y) (fun _ => b) id e
    (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j)
  exact h.trans (eval_relatedFormula _ r x y _)

/-- Free variables are [second class, first class, representatives, relation, b, target-edge representative]. -/
def prunedClassEdgeFormula : Formula 6 :=
  .ex (.ex (.conj (.member 1 4) (.conj (.member 0 4)
    (.conj (graphClassFormula 3 1 4 5) (.conj (graphClassFormula 2 0 4 5)
      (prunedRelatedFormula 6 7 1 0))))))

theorem eval_prunedClassEdgeFormula (base : BaseCollection s) (b a m r c d : U) :
    Eval s prunedClassEdgeFormula (cons d (cons c (cons a (cons m (cons b (cons r Fin.elim0)))))) ↔
      ∃ x y, s x a ∧ s y a ∧ GraphClassCode s a m x c ∧ GraphClassCode s a m y d ∧
        CodedRelation (prunedMember base b) (prunedCode base b r) (prunedCode base b x) (prunedCode base b y) := by
  simp only [prunedClassEdgeFormula, Eval, eval_graphClassFormula, eval_prunedRelatedFormula base]
  rfl

theorem pruned_graph_presentation_edges (base : BaseCollection s) {b : U} {A : PrunedQuotient base b}
    (P : PrunedNodePresentation base b A) (R : PrunedQuotient base b) :
    ∃ e, GraphCode s P.nodes e ∧ ∀ c d X Y,
      PrunedNodeCorresponds P c X → PrunedNodeCorresponds P d Y →
      (CodedRelation s e c d ↔ CodedRelation (prunedMember base b) R X Y) := by
  obtain ⟨r, _, rfl⟩ := pruned_good_representative base b R
  obtain ⟨e, heG, he⟩ := normalized_relation_comprehension base prunedClassEdgeFormula
    (cons P.representatives (cons P.relation (cons b (cons r Fin.elim0)))) P.nodes
  refine ⟨e, heG, ?_⟩
  intro c d X Y hc hd
  obtain ⟨x, hx, hxc, rfl⟩ := hc
  obtain ⟨y, hy, hyd, rfl⟩ := hd
  have hei := he c d
  rw [eval_prunedClassEdgeFormula base] at hei
  constructor
  · intro h
    obtain ⟨_, _, x', y', hx', hy', hx'c, hy'd, hxy⟩ := hei.mp h
    have hqx := (pruned_node_class_eq base P hx' hx hx'c hxc).mp rfl
    have hqy := (pruned_node_class_eq base P hy' hy hy'd hyd).mp rfl
    exact hqx ▸ hqy ▸ hxy
  · intro h
    exact hei.mpr ⟨(P.nodes_iff c).mpr ⟨x, hx, hxc⟩, (P.nodes_iff d).mpr ⟨y, hy, hyd⟩,
      x, y, hx, hy, hxc, hyd, h⟩

theorem pruned_graph_presentation_extensional (base : BaseCollection s) {b : U} (hbb : s b b)
    {A R : PrunedQuotient base b} (P : PrunedNodePresentation base b A) {e : U}
    (he : ∀ c d X Y, PrunedNodeCorresponds P c X → PrunedNodeCorresponds P d Y →
      (CodedRelation s e c d ↔ CodedRelation (prunedMember base b) R X Y))
    (hExt : GraphExtensionalCode (prunedMember base b) A R) : GraphExtensionalCode s P.nodes e := by
  intro c hc d hd hrows
  obtain ⟨X, hXA, hcX⟩ := (pruned_node_correspondence_total base hbb P).1 c hc
  obtain ⟨Y, hYA, hdY⟩ := (pruned_node_correspondence_total base hbb P).1 d hd
  apply (pruned_node_correspondence_eq base P hcX hdY).mpr
  apply hExt X hXA Y hYA
  intro Z hZA
  obtain ⟨z, hz, hzZ⟩ := (pruned_node_correspondence_total base hbb P).2 Z hZA
  exact (he c z X Z hcX hzZ).symm.trans ((hrows z hz).trans (he d z Y Z hdY hzZ))

/-- Full source presentation of an arbitrary target extensional graph. The
    target decoration and prescribed fixed-part extension are separate tasks. -/
theorem pruned_target_extensional_graph_lift (base : BaseCollection s) {b : U} (hbb : s b b)
    (A R : PrunedQuotient base b) (hExt : GraphExtensionalCode (prunedMember base b) A R) :
    ∃ P : PrunedNodePresentation base b A, ∃ e, GraphCode s P.nodes e ∧ GraphExtensionalCode s P.nodes e ∧
      ∀ c d X Y, PrunedNodeCorresponds P c X → PrunedNodeCorresponds P d Y →
        (CodedRelation s e c d ↔ CodedRelation (prunedMember base b) R X Y) := by
  obtain ⟨P⟩ := pruned_node_presentation_exists base hbb A
  obtain ⟨e, heG, he⟩ := pruned_graph_presentation_edges base P R
  exact ⟨P, e, heG, pruned_graph_presentation_extensional base hbb P he hExt, he⟩

#print axioms pruned_target_extensional_graph_lift
end FullBridge
