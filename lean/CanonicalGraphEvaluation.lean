import PrunedChoiceModelBridge
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Restrict an actual decoration to an actual transitive source subset. -/
theorem induced_decoration_restriction (base : BaseCollection s) {n}
    (p : Formula (n + 2)) (v : Fin n → U)
    (hmem : ∀ x y, FormulaEdges s p v x y → s y x)
    {a d ea ed g : U} (ha : TransitiveCode s a) (had : Subset s a d)
    (hEa : InducedEdgesCode s p v a ea) (hEd : InducedEdgesCode s p v d ed)
    (hg : DecorationCode s d ed g) :
    ∃ f, DecorationCode s a ea f ∧
      ∀ x y, CodedRelation s f x y ↔ s x a ∧ CodedRelation s g x y := by
  obtain ⟨f, hf, hr⟩ := function_domain_restriction base hg.1 had
  refine ⟨f, ⟨hf, ?_⟩, hr⟩
  intro x hx z hxz w
  have hxzg := ((hr x z).mp hxz).2
  constructor
  · intro hwz
    obtain ⟨y, _, hxy, hyw⟩ := (hg.2 x (had x hx) z hxzg w).mp hwz
    have hE := ((hEd.2 x y).mp hxy).2.2
    have hy := ha x hx y (hmem x y hE)
    exact ⟨y, hy, (hEa.2 x y).mpr ⟨hx, hy, hE⟩, (hr y w).mpr ⟨hy, hyw⟩⟩
  · rintro ⟨y, hy, hxy, hyw⟩
    exact (hg.2 x (had x hx) z hxzg w).mpr ⟨y, had y hy,
      (hEd.2 x y).mpr ⟨had x hx, had y hy, ((hEa.2 x y).mp hxy).2.2⟩,
      ((hr y w).mp hyw).2⟩

def DefinedDecorationValue {n} (s : U → U → Prop) (p : Formula (n + 2))
    (params : Fin n → U) (x z : U) : Prop :=
  ∃ c e f, TransitiveCode s c ∧ s x c ∧ InducedEdgesCode s p params c e ∧
    DecorationCode s c e f ∧ CodedRelation s f x z

/-- Free variables are [value, node, graph parameters]. -/
def globalDecorationFormula {n} (p : Formula (n + 2)) : Formula (n + 2) :=
  .ex (.ex (.ex (.conj (transitiveFormula 2) (.conj (.member 4 2)
    (.conj ((inducedEdgesFormula p).rename globalEdgeRename)
      (.conj (decorationCodeFormula 2 1 0) (relatedFormula 0 4 3)))))))

theorem eval_globalDecorationFormula {n} (p : Formula (n + 2)) (params : Fin n → U) (x z : U) :
    Eval s (globalDecorationFormula p) (cons z (cons x params)) ↔
      DefinedDecorationValue s p params x z := by
  simp only [globalDecorationFormula, Eval, eval_transitiveFormula, eval_rename,
    global_edge_env, eval_inducedEdgesFormula, eval_decorationCodeFormula, eval_relatedFormula, DefinedDecorationValue]
  rfl

theorem defined_decoration_value_exists (base : BaseCollection s) (hA : AFACode s) {n}
    (p : Formula (n + 2)) (params : Fin n → U) (x : U) :
    ∃ z, DefinedDecorationValue s p params x z := by
  obtain ⟨c, hc, hx⟩ := transitive_sets_cover base x
  obtain ⟨e, hG, he⟩ := normalized_relation_comprehension base p params c
  obtain ⟨f, hf, _⟩ := hA c e hG
  obtain ⟨z, hxz, _⟩ := hf.1.2 x hx
  exact ⟨z, c, e, f, hc, hx, ⟨hG, he⟩, hf, hxz⟩

/-- Uniqueness is obtained by restriction of a solution on a common actual
    transitive cover, not by an unproved solution of a proper-class graph. -/
theorem defined_decoration_value_unique (base : BaseCollection s) (hA : AFACode s) {n}
    (p : Formula (n + 2)) (params : Fin n → U)
    (hmem : ∀ x y, FormulaEdges s p params x y → s y x)
    {x z w : U} (hz : DefinedDecorationValue s p params x z)
    (hw : DefinedDecorationValue s p params x w) : z = w := by
  obtain ⟨a, ea, f, ha, hxa, hEa, hf, hxz⟩ := hz
  obtain ⟨b, eb, g, hb, hxb, hEb, hg, hxw⟩ := hw
  obtain ⟨d, _, had, hbd⟩ := transitive_sets_directed base ha hb
  obtain ⟨ed, hGd, hEd⟩ := normalized_relation_comprehension base p params d
  obtain ⟨k, hk, _⟩ := hA d ed hGd
  obtain ⟨fa, hfa, hfaR⟩ := induced_decoration_restriction base p params hmem ha had hEa ⟨hGd, hEd⟩ hk
  obtain ⟨gb, hgb, hgbR⟩ := induced_decoration_restriction base p params hmem hb hbd hEb ⟨hGd, hEd⟩ hk
  obtain ⟨ka, _, hua⟩ := hA a ea hEa.1
  obtain ⟨kb, _, hub⟩ := hA b eb hEb.1
  have hffa : f = fa := (hua f hf).trans (hua fa hfa).symm
  have hggb : g = gb := (hub g hg).trans (hub gb hgb).symm
  have hxzk : CodedRelation s k x z := ((hfaR x z).mp (hffa ▸ hxz)).2
  have hxwk : CodedRelation s k x w := ((hgbR x w).mp (hggb ▸ hxw)).2
  exact coded_function_value_unique hk.1 hxzk hxwk

noncomputable def canonicalGraphValue (base : BaseCollection s) (hA : AFACode s) {n}
    (p : Formula (n + 2)) (params : Fin n → U) (x : U) : U :=
  Classical.choose (defined_decoration_value_exists base hA p params x)

theorem canonical_graph_value_spec (base : BaseCollection s) (hA : AFACode s) {n}
    (p : Formula (n + 2)) (params : Fin n → U) (x : U) :
    DefinedDecorationValue s p params x (canonicalGraphValue base hA p params x) :=
  Classical.choose_spec (defined_decoration_value_exists base hA p params x)

theorem canonical_graph_value_iff (base : BaseCollection s) (hA : AFACode s) {n}
    (p : Formula (n + 2)) (params : Fin n → U)
    (hmem : ∀ x y, FormulaEdges s p params x y → s y x) (x z : U) :
    DefinedDecorationValue s p params x z ↔ canonicalGraphValue base hA p params x = z := by
  constructor
  · intro hz
    exact defined_decoration_value_unique base hA p params hmem
      (canonical_graph_value_spec base hA p params x) hz
  · intro hz
    exact hz ▸ canonical_graph_value_spec base hA p params x

theorem canonical_graph_value_rows (base : BaseCollection s) (hA : AFACode s) {n}
    (p : Formula (n + 2)) (params : Fin n → U)
    (hmem : ∀ x y, FormulaEdges s p params x y → s y x) (x z : U) :
    s z (canonicalGraphValue base hA p params x) ↔
      ∃ y, FormulaEdges s p params x y ∧ canonicalGraphValue base hA p params y = z := by
  obtain ⟨c, e, f, hc, hx, hE, hf, hxv⟩ := canonical_graph_value_spec base hA p params x
  constructor
  · intro hz
    obtain ⟨y, hy, hxy, hyz⟩ := (hf.2 x hx _ hxv z).mp hz
    exact ⟨y, ((hE.2 x y).mp hxy).2.2,
      (canonical_graph_value_iff base hA p params hmem y z).mp ⟨c, e, f, hc, hy, hE, hf, hyz⟩⟩
  · rintro ⟨y, hxy, hyz⟩
    have hy := hc x hx y (hmem x y hxy)
    obtain ⟨w, hyw, _⟩ := hf.1.2 y hy
    have hyw' := (canonical_graph_value_iff base hA p params hmem y w).mp ⟨c, e, f, hc, hy, hE, hf, hyw⟩
    have hwz := hyw'.symm.trans hyz
    exact (hf.2 x hx _ hxv z).mpr ⟨y, hy, (hE.2 x y).mpr ⟨hx, hy, hxy⟩, hwz ▸ hyw⟩

/-- Actual graph of the canonical evaluation on any source set. Collection is
    applied to its verified formula, not an arbitrary external predicate. -/
theorem canonical_graph_value_function (base : BaseCollection s) (hA : AFACode s) {n}
    (p : Formula (n + 2)) (params : Fin n → U)
    (hmem : ∀ x y, FormulaEdges s p params x y → s y x) (a : U) :
    ∃ f, FunctionCode s a f ∧ ∀ x z, CodedRelation s f x z ↔
      s x a ∧ canonicalGraphValue base hA p params x = z := by
  obtain ⟨B, hB⟩ := base.collection n (globalDecorationFormula p) params a (by
    intro x _
    obtain ⟨z, hz⟩ := defined_decoration_value_exists base hA p params x
    exact ⟨z, (eval_globalDecorationFormula p params x z).mpr hz⟩)
  obtain ⟨u, hu⟩ := binary_union_exists base.pairing base.union a B
  obtain ⟨r, hmemr⟩ := relation_comprehension_members base (globalDecorationFormula p) params u
  obtain ⟨f, hfmem⟩ := base.separation 1
    (.ex (.ex (.conj (.member 1 3) (orderedPairFormula 2 1 0)))) (cons a Fin.elim0) r
  have hfmem' : ∀ t, s t f ↔ s t r ∧ ∃ x z, s x a ∧ IsOrderedPair s t x z := by
    intro t
    have h := hfmem t
    simp only [Eval, eval_orderedPairFormula] at h
    exact h
  have hf : ∀ x z, CodedRelation s f x z ↔ s x a ∧ canonicalGraphValue base hA p params x = z := by
    intro x z
    constructor
    · rintro ⟨t, ht, htxz⟩
      obtain ⟨htr, x', z', hx', htxz'⟩ := (hfmem' t).mp ht
      obtain ⟨rfl, rfl⟩ := orderedPair_injective htxz htxz'
      obtain ⟨x', z', _, _, hp, hev⟩ := (hmemr t).mp htr
      obtain ⟨rfl, rfl⟩ := orderedPair_injective htxz hp
      exact ⟨hx', (canonical_graph_value_iff base hA p params hmem x z).mp
        ((eval_globalDecorationFormula p params x z).mp hev)⟩
    · rintro ⟨hx, hv⟩
      obtain ⟨w, hwB, hev⟩ := hB x hx
      have hw := (canonical_graph_value_iff base hA p params hmem x w).mp
        ((eval_globalDecorationFormula p params x w).mp hev)
      have hwz := hw.symm.trans hv
      have hzB : s z B := hwz ▸ hwB
      have hevz : Eval s (globalDecorationFormula p) (cons z (cons x params)) := hwz ▸ hev
      obtain ⟨t, ht⟩ := orderedPair_exists base.pairing x z
      exact ⟨t, (hfmem' t).mpr ⟨(hmemr t).mpr ⟨x, z, (hu x).mpr (Or.inl hx),
        (hu z).mpr (Or.inr hzB), ht, hevz⟩, x, z, hx, ht⟩, ht⟩
  refine ⟨f, ⟨?_, ?_⟩, hf⟩
  · intro t ht
    exact ((hfmem' t).mp ht).2
  · intro x hx
    exact ⟨canonicalGraphValue base hA p params x, (hf x _).mpr ⟨hx, rfl⟩,
      fun z hz => ((hf x z).mp hz).2.symm⟩

theorem canonical_graph_value_decoration (base : BaseCollection s) (hA : AFACode s) {n}
    (p : Formula (n + 2)) (params : Fin n → U)
    (hmem : ∀ x y, FormulaEdges s p params x y → s y x)
    {c e : U} (hc : TransitiveCode s c) (hE : InducedEdgesCode s p params c e) :
    ∃ f, DecorationCode s c e f ∧ ∀ x z, CodedRelation s f x z ↔
      s x c ∧ canonicalGraphValue base hA p params x = z := by
  obtain ⟨f, hf, hr⟩ := canonical_graph_value_function base hA p params hmem c
  refine ⟨f, ⟨hf, ?_⟩, hr⟩
  intro x hx z hxz w
  have hz := ((hr x z).mp hxz).2
  have hrow := canonical_graph_value_rows base hA p params hmem x w
  rw [hz] at hrow
  refine hrow.trans ⟨?_, ?_⟩
  · rintro ⟨y, hxy, hyw⟩
    have hy := hc x hx y (hmem x y hxy)
    exact ⟨y, hy, (hE.2 x y).mpr ⟨hx, hy, hxy⟩, (hr y w).mpr ⟨hy, hyw⟩⟩
  · rintro ⟨y, _, hxy, hyw⟩
    exact ⟨y, ((hE.2 x y).mp hxy).2.2, ((hr y w).mp hyw).2⟩

/-- The canonical AFA evaluation identifies every pair identified by the least
    extensionalization, via an actual closed-domain map with extensional range. -/
theorem canonical_graph_value_respects_least (base : BaseCollection s) (hA : AFACode s) {n}
    (p : Formula (n + 2)) (params : Fin n → U)
    (hmem : ∀ x y, FormulaEdges s p params x y → s y x)
    {x y : U} (hxy : DefinedLeastRelation s p params x y) :
    canonicalGraphValue base hA p params x = canonicalGraphValue base hA p params y := by
  obtain ⟨a, ha, hxa⟩ := transitive_sets_cover base x
  obtain ⟨b, hb, hyb⟩ := transitive_sets_cover base y
  obtain ⟨c, hc, hac, hbc⟩ := transitive_sets_directed base ha hb
  obtain ⟨e, hG, he⟩ := normalized_relation_comprehension base p params c
  obtain ⟨f, hf, hfr⟩ := canonical_graph_value_decoration base hA p params hmem hc ⟨hG, he⟩
  obtain ⟨T, hT, hRange⟩ := decoration_transitive_range base hf
  obtain ⟨eT, _, _, _, heT, _⟩ := membership_graph_identity_decoration base hT
  have hin : ∀ u v, CodedRelation s f u v → s v T :=
    fun u v huv => (hRange v).mpr ⟨u, coded_function_domain hf.1 huv, huv⟩
  have hExt : GraphExtensionalCode s T eT := by
    intro u hu v hv hrows
    apply base.extensional
    intro z
    constructor
    · intro hzu
      exact ((heT v z).mp ((hrows z (hT u hu z hzu)).mp ((heT u z).mpr ⟨hu, hzu⟩))).2
    · intro hzv
      exact ((heT u z).mp ((hrows z (hT v hv z hzv)).mpr ((heT v z).mpr ⟨hv, hzv⟩))).2
  have hrows : ∀ u v, s u c → CodedRelation s f u v → ∀ w, s w T →
      (CodedRelation s eT v w ↔ ∃ z, FormulaEdges s p params u z ∧ CodedRelation s f z w) := by
    intro u v hu huv w _
    refine (heT v w).trans ⟨?_, ?_⟩
    · intro hvw
      obtain ⟨z, _, huz, hzw⟩ := (hf.2 u hu v huv w).mp hvw.2
      exact ⟨z, ((he u z).mp huz).2.2, hzw⟩
    · rintro ⟨z, huz, hzw⟩
      have hz := hc u hu z (hmem u z huz)
      exact ⟨hin u v huv, (hf.2 u hu v huv w).mpr ⟨z, hz, (he u z).mpr ⟨hu, hz, huz⟩, hzw⟩⟩
  exact global_least_conserves_closed_map base p params hmem hf.1 hin
    (fun u hu z huz => hc u hu z (hmem u z huz)) hExt hrows
    ((hfr x _).mpr ⟨hac x hxa, rfl⟩) ((hfr y _).mpr ⟨hbc y hyb, rfl⟩) hxy

#print axioms canonical_graph_value_function
#print axioms canonical_graph_value_respects_least
end FullBridge
