import FunctionalNormalization
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A set of nodes closed under all outgoing graph edges. -/
def GraphClosedCode (s : U → U → Prop) (a e c : U) : Prop :=
  Subset s c a ∧ ∀ x, s x c → ∀ y, CodedRelation s e x y → s y c

def graphClosedFormula {n} (a e c : Fin n) : Formula n :=
  .conj (.all (.impl (.member 0 c.succ) (.member 0 a.succ)))
    (.all (.impl (.member 0 c.succ)
      (.all (.impl (relatedFormula e.succ.succ 1 0) (.member 0 c.succ.succ)))))

theorem eval_graphClosedFormula (s : U → U → Prop) {n}
    (a e c : Fin n) (v : Fin n → U) :
    Eval s (graphClosedFormula a e c) v ↔ GraphClosedCode s (v a) (v e) (v c) := by
  simp only [graphClosedFormula, Eval, eval_relatedFormula, GraphClosedCode, Subset]
  rfl

theorem least_relation_preserves_closed_extensional (base : BaseCollection s)
    {a e m c : U} (hc : GraphClosedCode s a e c)
    (hExt : GraphExtensionalCode s c e) (hm : LeastGraphRelationCode s a e m)
    {x y : U} (hx : s x c) (hy : s y c) (hxy : CodedRelation s m x y) : x = y := by
  obtain ⟨k, hkG, hk⟩ := normalized_relation_comprehension base
    (Formula.impl (.conj (.member 1 2) (.member 0 2)) (.equal 1 0))
    (cons c Fin.elim0) a
  have hki : ∀ u v, CodedRelation s k u v ↔ s u a ∧ s v a ∧
      (s u c ∧ s v c → u = v) := by
    intro u v
    have h := hk u v
    simp only [Eval] at h
    exact h
  have hkp : GraphPreFixedCode s a e k := by
    refine ⟨hkG, fun u hu => (hki u u).mpr ⟨hu, hu, fun _ => rfl⟩, ?_⟩
    intro u v hu hv hmuv
    refine (hki u v).mpr ⟨hu, hv, ?_⟩
    rintro ⟨huc, hvc⟩
    apply hExt u huc v hvc
    intro w _
    constructor
    · intro huw
      obtain ⟨z, hvz, hwz⟩ := hmuv.1 w huw
      have hwzc := ((hki w z).mp hwz).2.2 ⟨hc.2 u huc w huw, hc.2 v hvc z hvz⟩
      exact hwzc.symm ▸ hvz
    · intro hvw
      obtain ⟨z, huz, hzw⟩ := hmuv.2 w hvw
      have hzwc := ((hki z w).mp hzw).2.2 ⟨hc.2 u huc z huz, hc.2 v hvc w hvw⟩
      exact hzwc ▸ huz
  exact ((hki x y).mp (hm.2 k hkp x y hxy)).2.2 ⟨hx, hy⟩

theorem least_classes_injective_on_closed (base : BaseCollection s)
    {a e m c x y X Y : U} (hG : GraphCode s a e)
    (hm : LeastGraphRelationCode s a e m) (hc : GraphClosedCode s a e c)
    (hExt : GraphExtensionalCode s c e) (hx : s x c) (hy : s y c)
    (hX : GraphClassCode s a m x X) (hY : GraphClassCode s a m y Y) :
    X = Y ↔ x = y := by
  constructor
  · intro hXY
    exact least_relation_preserves_closed_extensional base hc hExt hm hx hy
      ((least_graph_class_eq_iff base hG hm (hc.1 x hx) (hc.1 y hy) hX hY).mp hXY)
  · intro hxy
    subst y
    exact graph_class_unique base hX hY

theorem least_quotient_reflects_closed_edges (base : BaseCollection s)
    {a e m c x y X Y : U} (hG : GraphCode s a e)
    (hm : LeastGraphRelationCode s a e m) (hc : GraphClosedCode s a e c)
    (hExt : GraphExtensionalCode s c e) (hx : s x c) (hy : s y c)
    (hX : GraphClassCode s a m x X) (hY : GraphClassCode s a m y Y) :
    GraphQuotientEdge s a m e X Y ↔ CodedRelation s e x y := by
  constructor
  · intro hXY
    obtain ⟨z, hz, hxz, hZ⟩ :=
      (least_graph_quotient_edge_from_representative base hG hm (hc.1 x hx) hX).mp hXY
    have hzy := (least_classes_injective_on_closed base hG hm hc hExt
      (hc.2 x hx z hxz) hy hZ hY).mp rfl
    exact hzy ▸ hxz
  · intro hxy
    exact ⟨x, y, hc.1 x hx, hc.1 y hy, hX, hY, hxy⟩

theorem parameter_graph_closed {a e t : U}
    (ht : TransitiveCode s t) (hend : EndExtensionCode s a e t) :
    GraphClosedCode s a e t := by
  exact ⟨hend.1, fun x hx y hxy => ht x hx y ((hend.2 x hx y).mp hxy)⟩

/-- One least quotient simultaneously embeds every closed extensional subgraph. -/
theorem least_quotient_preserves_all_closed (base : BaseCollection s)
    {a e : U} (hG : GraphCode s a e) :
    ∃ m b r, LeastGraphRelationCode s a e m ∧
      (∀ X, s X b ↔ ∃ x, s x a ∧ GraphClassCode s a m x X) ∧
      GraphCode s b r ∧ GraphExtensionalCode s b r ∧
      (∀ X Y, CodedRelation s r X Y ↔ GraphQuotientEdge s a m e X Y) ∧
      ∀ c, GraphClosedCode s a e c → GraphExtensionalCode s c e →
        ∀ x y X Y, s x c → s y c → GraphClassCode s a m x X →
          GraphClassCode s a m y Y →
          (X = Y ↔ x = y) ∧ (CodedRelation s r X Y ↔ CodedRelation s e x y) := by
  obtain ⟨m, b, r, hm, hb, hrG, hr, hrExt⟩ := least_extensional_graph_quotient_exists base hG
  refine ⟨m, b, r, hm, hb, hrG, hrExt, hr, ?_⟩
  intro c hc hExt x y X Y hx hy hX hY
  exact ⟨least_classes_injective_on_closed base hG hm hc hExt hx hy hX hY,
    (hr X Y).trans (least_quotient_reflects_closed_edges base hG hm hc hExt hx hy hX hY)⟩

#print axioms least_quotient_preserves_all_closed
end FullBridge
