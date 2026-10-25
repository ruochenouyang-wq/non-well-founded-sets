import GraphClasses
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def GraphQuotientEdge (s : U → U → Prop) (a m e c d : U) : Prop :=
  ∃ x y, s x a ∧ s y a ∧ GraphClassCode s a m x c ∧
    GraphClassCode s a m y d ∧ CodedRelation s e x y

def graphQuotientEdgeFormula : Formula 5 :=
  .ex (.ex (.conj (.member 1 4) (.conj (.member 0 4)
    (.conj (graphClassFormula 3 1 4 5)
      (.conj (graphClassFormula 2 0 4 5) (relatedFormula 6 1 0))))))

theorem eval_graphQuotientEdgeFormula (d c a m e : U) :
    Eval s graphQuotientEdgeFormula (cons d (cons c (cons a (cons m (cons e Fin.elim0))))) ↔
      GraphQuotientEdge s a m e c d := by
  simp only [graphQuotientEdgeFormula, Eval, eval_graphClassFormula, eval_relatedFormula]
  rfl

theorem graph_quotient_edges_exists (base : BaseCollection s) {a m b : U} (e : U)
    (hb : ∀ c, s c b ↔ ∃ x, s x a ∧ GraphClassCode s a m x c) :
    ∃ r, GraphCode s b r ∧ ∀ c d, CodedRelation s r c d ↔ GraphQuotientEdge s a m e c d := by
  obtain ⟨r, hG, hr⟩ := normalized_relation_comprehension base graphQuotientEdgeFormula
    (cons a (cons m (cons e Fin.elim0))) b
  refine ⟨r, hG, ?_⟩
  intro c d
  have h := hr c d
  rw [eval_graphQuotientEdgeFormula] at h
  constructor
  · intro hcd
    exact (h.mp hcd).2.2
  · intro hcd
    obtain ⟨x, y, hx, hy, hc, hd, he⟩ := hcd
    exact h.mpr ⟨(hb c).mpr ⟨x, hx, hc⟩, (hb d).mpr ⟨y, hy, hd⟩, x, y, hx, hy, hc, hd, he⟩

theorem graph_quotient_edge_from_representative (base : BaseCollection s)
    {a m e x c d : U} (hG : GraphCode s a e) (hm : MaxGraphBisimCode s a e m)
    (hx : s x a) (hc : GraphClassCode s a m x c) :
    GraphQuotientEdge s a m e c d ↔
      ∃ y, s y a ∧ CodedRelation s e x y ∧ GraphClassCode s a m y d := by
  constructor
  · rintro ⟨x', y', hx', hy', hc', hd', hxy'⟩
    have hxx' := (graph_class_eq_iff base hG hm hx hx' hc hc').mp rfl
    obtain ⟨y, hxy, hyy'⟩ := (hm.1.2 x x' hxx').2 y' hxy'
    have hy := (graphCode_endpoints hG hxy).2
    obtain ⟨d', hd⟩ := graph_class_exists base a m y
    have heq := (graph_class_eq_iff base hG hm hy hy' hd hd').mpr hyy'
    exact ⟨y, hy, hxy, heq ▸ hd⟩
  · rintro ⟨y, hy, hxy, hd⟩
    exact ⟨x, y, hx, hy, hc, hd, hxy⟩

theorem graph_quotient_extensional (base : BaseCollection s)
    {a m e b r : U} (hG : GraphCode s a e) (hm : MaxGraphBisimCode s a e m)
    (hb : ∀ c, s c b ↔ ∃ x, s x a ∧ GraphClassCode s a m x c)
    (hr : ∀ c d, CodedRelation s r c d ↔ GraphQuotientEdge s a m e c d) :
    GraphExtensionalCode s b r := by
  intro c hcb d hdb hrows
  obtain ⟨x, hx, hc⟩ := (hb c).mp hcb
  obtain ⟨y, hy, hd⟩ := (hb d).mp hdb
  apply (graph_class_eq_iff base hG hm hx hy hc hd).mpr
  apply maximal_graph_bisim_of_children base hm hx hy
  · intro u hxu
    have hu := (graphCode_endpoints hG hxu).2
    obtain ⟨k, hk⟩ := graph_class_exists base a m u
    have hck := (hr c k).mpr ⟨x, u, hx, hu, hc, hk, hxu⟩
    have hdk := (hrows k ((hb k).mpr ⟨u, hu, hk⟩)).mp hck
    obtain ⟨v, hv, hyv, hvk⟩ :=
      (graph_quotient_edge_from_representative base hG hm hy hd).mp ((hr d k).mp hdk)
    exact ⟨v, hyv, (graph_class_eq_iff base hG hm hu hv hk hvk).mp rfl⟩
  · intro v hyv
    have hv := (graphCode_endpoints hG hyv).2
    obtain ⟨k, hk⟩ := graph_class_exists base a m v
    have hdk := (hr d k).mpr ⟨y, v, hy, hv, hd, hk, hyv⟩
    have hck := (hrows k ((hb k).mpr ⟨v, hv, hk⟩)).mpr hdk
    obtain ⟨u, hu, hxu, huk⟩ :=
      (graph_quotient_edge_from_representative base hG hm hx hc).mp ((hr c k).mp hck)
    exact ⟨u, hxu, (graph_class_eq_iff base hG hm hu hv huk hk).mp rfl⟩

theorem graph_quotient_realization (base : BaseCollection s) (hBAFA : BAFACode s)
    {a e : U} (hG : GraphCode s a e) :
    ∃ m b r f, MaxGraphBisimCode s a e m ∧
      (∀ c, s c b ↔ ∃ x, s x a ∧ GraphClassCode s a m x c) ∧
      GraphCode s b r ∧
      (∀ c d, CodedRelation s r c d ↔ GraphQuotientEdge s a m e c d) ∧
      GraphExtensionalCode s b r ∧ DecorationCode s b r f ∧ InjectiveCode s f := by
  obtain ⟨m, hm⟩ := maximal_graph_bisim_exists base a e
  obtain ⟨b, hb⟩ := graph_class_nodes_exists base a m
  obtain ⟨r, hrG, hr⟩ := graph_quotient_edges_exists base e hb
  have hext := graph_quotient_extensional base hG hm hb hr
  obtain ⟨f, hf, hi⟩ := bafa_extensional_realization base.empty hBAFA b r hrG hext
  exact ⟨m, b, r, f, hm, hb, hrG, hr, hext, hf, hi⟩

#print axioms graph_quotient_realization
end FullBridge
