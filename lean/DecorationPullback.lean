import GraphQuotient
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def pullbackFormula : Formula 5 :=
  .conj (.member 1 2) (.ex (.conj (graphClassFormula 0 2 3 4) (relatedFormula 5 0 1)))

theorem eval_pullbackFormula (y x a m f : U) :
    Eval s pullbackFormula (cons y (cons x (cons a (cons m (cons f Fin.elim0))))) ↔
      s x a ∧ ∃ c, GraphClassCode s a m x c ∧ CodedRelation s f c y := by
  simp only [pullbackFormula, Eval, eval_graphClassFormula, eval_relatedFormula]
  rfl

theorem graph_class_pullback_exists (base : BaseCollection s) (a m f : U) :
    ∃ g, (∀ p, s p g → ∃ x y, s x a ∧ IsOrderedPair s p x y) ∧
      ∀ x y, CodedRelation s g x y ↔
        s x a ∧ ∃ c, GraphClassCode s a m x c ∧ CodedRelation s f c y := by
  obtain ⟨d₀, hd₀⟩ := codedRelation_component_bound base.union f
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union a d₀
  obtain ⟨g, hg⟩ := relation_comprehension_members base pullbackFormula
    (cons a (cons m (cons f Fin.elim0))) d
  have hmembers : ∀ p, s p g ↔ ∃ x y, s x a ∧ IsOrderedPair s p x y ∧
      ∃ c, GraphClassCode s a m x c ∧ CodedRelation s f c y := by
    intro p
    have h := hg p
    constructor
    · intro hp
      obtain ⟨x, y, _, _, hpxy, hev⟩ := h.mp hp
      obtain ⟨hx, hc⟩ := (eval_pullbackFormula y x a m f).mp hev
      exact ⟨x, y, hx, hpxy, hc⟩
    · rintro ⟨x, y, hx, hpxy, c, hc, hf⟩
      exact h.mpr ⟨x, y, (hd x).mpr (Or.inl hx), (hd y).mpr (Or.inr (hd₀ c y hf).2),
        hpxy, (eval_pullbackFormula y x a m f).mpr ⟨hx, c, hc, hf⟩⟩
  refine ⟨g, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, y, hx, hpxy, _⟩ := (hmembers p).mp hp
    exact ⟨x, y, hx, hpxy⟩
  · intro x y
    constructor
    · rintro ⟨p, hp, hpxy⟩
      obtain ⟨x', y', hx, hp', hc⟩ := (hmembers p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxy hp'
      exact ⟨hx, hc⟩
    · rintro ⟨hx, hc⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x y
      exact ⟨p, (hmembers p).mpr ⟨x, y, hx, hp, hc⟩, hp⟩

theorem graph_class_pullback_function (base : BaseCollection s)
    {a m b f g : U}
    (hb : ∀ c, s c b ↔ ∃ x, s x a ∧ GraphClassCode s a m x c)
    (hf : FunctionCode s b f)
    (hgmem : ∀ p, s p g → ∃ x y, s x a ∧ IsOrderedPair s p x y)
    (hg : ∀ x y, CodedRelation s g x y ↔
      s x a ∧ ∃ c, GraphClassCode s a m x c ∧ CodedRelation s f c y) :
    FunctionCode s a g := by
  refine ⟨hgmem, ?_⟩
  intro x hx
  obtain ⟨c, hc⟩ := graph_class_exists base a m x
  obtain ⟨y, hfy, huniq⟩ := hf.2 c ((hb c).mpr ⟨x, hx, hc⟩)
  refine ⟨y, (hg x y).mpr ⟨hx, c, hc, hfy⟩, ?_⟩
  intro z hgz
  obtain ⟨_, c', hc', hfz⟩ := (hg x z).mp hgz
  have heq := graph_class_unique base hc' hc
  subst c'
  exact huniq z hfz

theorem graph_class_pullback_decoration (base : BaseCollection s)
    {a e m b r f g : U} (hG : GraphCode s a e) (hm : MaxGraphBisimCode s a e m)
    (hb : ∀ c, s c b ↔ ∃ x, s x a ∧ GraphClassCode s a m x c)
    (hr : ∀ c d, CodedRelation s r c d ↔ GraphQuotientEdge s a m e c d)
    (hf : DecorationCode s b r f)
    (hgmem : ∀ p, s p g → ∃ x y, s x a ∧ IsOrderedPair s p x y)
    (hg : ∀ x y, CodedRelation s g x y ↔
      s x a ∧ ∃ c, GraphClassCode s a m x c ∧ CodedRelation s f c y) :
    DecorationCode s a e g := by
  refine ⟨graph_class_pullback_function base hb hf.1 hgmem hg, ?_⟩
  intro x hx v hxv w
  obtain ⟨_, c, hc, hfcv⟩ := (hg x v).mp hxv
  have hcb := (hb c).mpr ⟨x, hx, hc⟩
  constructor
  · intro hwv
    obtain ⟨d, _, hrcd, hfdw⟩ := (hf.2 c hcb v hfcv w).mp hwv
    obtain ⟨y, hy, hexy, hdy⟩ :=
      (graph_quotient_edge_from_representative base hG hm hx hc).mp ((hr c d).mp hrcd)
    exact ⟨y, hy, hexy, (hg y w).mpr ⟨hy, d, hdy, hfdw⟩⟩
  · rintro ⟨y, hy, hexy, hgyw⟩
    obtain ⟨_, d, hdy, hfdw⟩ := (hg y w).mp hgyw
    exact (hf.2 c hcb v hfcv w).mpr ⟨d, (hb d).mpr ⟨y, hy, hdy⟩,
      (hr c d).mpr ⟨x, y, hx, hy, hc, hdy, hexy⟩, hfdw⟩

def GraphSolvabilityCode (s : U → U → Prop) : Prop :=
  ∀ a e, GraphCode s a e → ∃ f, DecorationCode s a e f

theorem bafa_graph_solvability (base : BaseCollection s) (hBAFA : BAFACode s) :
    GraphSolvabilityCode s := by
  intro a e hG
  obtain ⟨m, b, r, f, hm, hb, _, hr, _, hf, _⟩ := graph_quotient_realization base hBAFA hG
  obtain ⟨g, hgmem, hg⟩ := graph_class_pullback_exists base a m f
  exact ⟨g, graph_class_pullback_decoration base hG hm hb hr hf hgmem hg⟩

#print axioms bafa_graph_solvability
end FullBridge
