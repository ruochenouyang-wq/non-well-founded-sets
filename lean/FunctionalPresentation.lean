import ChoiceFactorization
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A set-coded function assigning a subset of a to each node of a. -/
def FunctionalGraphCode (s : U → U → Prop) (a h : U) : Prop :=
  FunctionCode s a h ∧ ∀ x c, CodedRelation s h x c → Subset s c a

/-- The graph e is the membership relation in the values of h. -/
def RowPresentation (s : U → U → Prop) (a e h : U) : Prop :=
  ∀ x y, CodedRelation s e x y ↔ s x a ∧ ∃ c, CodedRelation s h x c ∧ s y c

def FunctionalDecorationCode (s : U → U → Prop) (a h g : U) : Prop :=
  FunctionCode s a g ∧ ∀ x, s x a → ∀ v, CodedRelation s g x v →
    ∀ w, s w v ↔ ∃ c y, CodedRelation s h x c ∧ s y c ∧ CodedRelation s g y w

def FunctionalFixedSolvabilityCode (s : U → U → Prop) : Prop :=
  ∀ t, TransitiveCode s t → ∀ a h, FunctionalGraphCode s a h → Subset s t a →
    (∀ x, s x t → CodedRelation s h x x) →
    ∃ g, FunctionalDecorationCode s a h g ∧ ∀ x, s x t → CodedRelation s g x x

def rowFunctionFormula : Formula 4 :=
  .conj (.member 1 2) (relationRowFormula 3 1 0)

theorem eval_rowFunctionFormula (s : U → U → Prop) (c x a e : U) :
    Eval s rowFunctionFormula (cons c (cons x (cons a (cons e Fin.elim0)))) ↔
      s x a ∧ RelationRow s e x c := by
  simp only [rowFunctionFormula, Eval, eval_relationRowFormula]
  rfl

theorem graph_functional_presentation (base : BaseCollection s) {a e : U}
    (hG : GraphCode s a e) :
    ∃ h, FunctionalGraphCode s a h ∧ RowPresentation s a e h := by
  obtain ⟨P, hP⟩ := base.powerset a
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union a P
  obtain ⟨h, hh⟩ := relation_comprehension_members base rowFunctionFormula
    (cons a (cons e Fin.elim0)) d
  have rowBound : ∀ x c, RelationRow s e x c → s c P := by
    intro x c hc
    exact (hP c).mpr (fun y hy => (graphCode_endpoints hG ((hc y).mp hy)).2)
  have hi : ∀ x c, CodedRelation s h x c ↔ s x a ∧ RelationRow s e x c := by
    intro x c
    constructor
    · rintro ⟨p, hp, hpxc⟩
      obtain ⟨x', c', _, _, hp', hev⟩ := (hh p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxc hp'
      exact (eval_rowFunctionFormula s c x a e).mp hev
    · rintro ⟨hx, hc⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x c
      exact ⟨p, (hh p).mpr ⟨x, c, (hd x).mpr (Or.inl hx),
        (hd c).mpr (Or.inr (rowBound x c hc)), hp,
        (eval_rowFunctionFormula s c x a e).mpr ⟨hx, hc⟩⟩, hp⟩
  refine ⟨h, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨x, c, _, _, hpair, hev⟩ := (hh p).mp hp
    exact ⟨x, c, ((eval_rowFunctionFormula s c x a e).mp hev).1, hpair⟩
  · intro x hx
    obtain ⟨c, hc⟩ := relation_row_exists base e x
    exact ⟨c, (hi x c).mpr ⟨hx, hc⟩,
      fun z hz => relation_row_unique base ((hi x z).mp hz).2 hc⟩
  · intro x c hxc y hy
    exact (graphCode_endpoints hG ((((hi x c).mp hxc).2 y).mp hy)).2
  · intro x y
    constructor
    · intro hxy
      obtain ⟨c, hc⟩ := relation_row_exists base e x
      have hx := (graphCode_endpoints hG hxy).1
      exact ⟨hx, c, (hi x c).mpr ⟨hx, hc⟩, (hc y).mpr hxy⟩
    · rintro ⟨_, c, hxc, hyc⟩
      exact (((hi x c).mp hxc).2 y).mp hyc

def functionalEdgeFormula : Formula 3 :=
  .ex (.conj (relatedFormula 3 2 0) (.member 1 0))

theorem eval_functionalEdgeFormula (s : U → U → Prop) (y x h : U) :
    Eval s functionalEdgeFormula (cons y (cons x (cons h Fin.elim0))) ↔
      ∃ c, CodedRelation s h x c ∧ s y c := by
  simp only [functionalEdgeFormula, Eval, eval_relatedFormula]
  rfl

theorem functional_graph_presentation (base : BaseCollection s) {a h : U}
    (hh : FunctionalGraphCode s a h) :
    ∃ e, GraphCode s a e ∧ RowPresentation s a e h := by
  obtain ⟨e, hG, he⟩ := normalized_relation_comprehension base functionalEdgeFormula
    (cons h Fin.elim0) a
  refine ⟨e, hG, ?_⟩
  intro x y
  have hi := he x y
  rw [eval_functionalEdgeFormula] at hi
  constructor
  · intro hxy
    exact ⟨(hi.mp hxy).1, (hi.mp hxy).2.2⟩
  · rintro ⟨hx, c, hxc, hyc⟩
    exact hi.mpr ⟨hx, hh.2 x c hxc y hyc, c, hxc, hyc⟩

theorem decoration_iff_functional {a e h g : U}
    (hh : FunctionalGraphCode s a h) (he : RowPresentation s a e h) :
    DecorationCode s a e g ↔ FunctionalDecorationCode s a h g := by
  constructor
  · rintro ⟨hg, hD⟩
    refine ⟨hg, ?_⟩
    intro x hx v hxv w
    rw [hD x hx v hxv w]
    constructor
    · rintro ⟨y, _, hxy, hyg⟩
      obtain ⟨_, c, hxc, hyc⟩ := (he x y).mp hxy
      exact ⟨c, y, hxc, hyc, hyg⟩
    · rintro ⟨c, y, hxc, hyc, hyg⟩
      exact ⟨y, hh.2 x c hxc y hyc, (he x y).mpr ⟨hx, c, hxc, hyc⟩, hyg⟩
  · rintro ⟨hg, hD⟩
    refine ⟨hg, ?_⟩
    intro x hx v hxv w
    rw [hD x hx v hxv w]
    constructor
    · rintro ⟨c, y, hxc, hyc, hyg⟩
      exact ⟨y, hh.2 x c hxc y hyc, (he x y).mpr ⟨hx, c, hxc, hyc⟩, hyg⟩
    · rintro ⟨y, _, hxy, hyg⟩
      obtain ⟨_, c, hxc, hyc⟩ := (he x y).mp hxy
      exact ⟨c, y, hxc, hyc, hyg⟩

theorem endExtension_iff_functional_fixed (base : BaseCollection s) {a e h t : U}
    (hh : FunctionalGraphCode s a h) (he : RowPresentation s a e h)
    (hta : Subset s t a) :
    EndExtensionCode s a e t ↔ ∀ x, s x t → CodedRelation s h x x := by
  constructor
  · intro hend x hx
    obtain ⟨c, hxc, hu⟩ := hh.1.2 x (hta x hx)
    have hc : c = x := by
      apply base.extensional
      intro y
      constructor
      · intro hyc
        exact (hend.2 x hx y).mp ((he x y).mpr ⟨hta x hx, c, hxc, hyc⟩)
      · intro hyx
        obtain ⟨_, d, hxd, hyd⟩ := (he x y).mp ((hend.2 x hx y).mpr hyx)
        exact hu d hxd ▸ hyd
    exact hc ▸ hxc
  · intro hfix
    refine ⟨hta, ?_⟩
    intro x hx y
    rw [he x y]
    constructor
    · rintro ⟨_, c, hxc, hyc⟩
      obtain ⟨v, _, hu⟩ := hh.1.2 x (hta x hx)
      have hcx := (hu c hxc).trans (hu x (hfix x hx)).symm
      exact hcx ▸ hyc
    · intro hyx
      exact ⟨hta x hx, x, hfix x hx, hyx⟩

theorem fixed_solvability_iff_functional (base : BaseCollection s) :
    FixedGraphSolvabilityCode s ↔ FunctionalFixedSolvabilityCode s := by
  constructor
  · intro hF t ht a h hh hta hfix
    obtain ⟨e, hG, he⟩ := functional_graph_presentation base hh
    have hend := (endExtension_iff_functional_fixed base hh he hta).mpr hfix
    obtain ⟨g, hg, hgfix⟩ := hF t ht a e hG hend
    exact ⟨g, (decoration_iff_functional hh he).mp hg, hgfix⟩
  · intro hF t ht a e hG hend
    obtain ⟨h, hh, he⟩ := graph_functional_presentation base hG
    have hfix := (endExtension_iff_functional_fixed base hh he hend.1).mp hend
    obtain ⟨g, hg, hgfix⟩ := hF t ht a h hh hend.1 hfix
    exact ⟨g, (decoration_iff_functional hh he).mpr hg, hgfix⟩

theorem eval_fixedSentence_functional (base : BaseCollection s) :
    Eval s fixedGraphSolvabilitySentence Fin.elim0 ↔ FunctionalFixedSolvabilityCode s :=
  (eval_fixedGraphSolvabilitySentence s).trans (fixed_solvability_iff_functional base)



theorem functional_row_contents {a e h x c : U}
    (hh : FunctionalGraphCode s a h) (he : RowPresentation s a e h)
    (hxc : CodedRelation s h x c) :
    s x a ∧ ∀ y, CodedRelation s e x y ↔ s y c := by
  obtain ⟨p, hp, hpxc⟩ := hxc
  obtain ⟨x', c', hx', hp'⟩ := hh.1.1 p hp
  obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxc hp'
  have hxc : CodedRelation s h x c := ⟨p, hp, hpxc⟩
  refine ⟨hx', ?_⟩
  intro y
  constructor
  · intro hxy
    obtain ⟨_, d, hxd, hyd⟩ := (he x y).mp hxy
    obtain ⟨v, _, hu⟩ := hh.1.2 x hx'
    have hdc := (hu d hxd).trans (hu c hxc).symm
    exact hdc ▸ hyd
  · intro hyc
    exact (he x y).mpr ⟨hx', c, hxc, hyc⟩

theorem graph_extensional_iff_row_injective (base : BaseCollection s) {a e h : U}
    (hh : FunctionalGraphCode s a h) (he : RowPresentation s a e h) :
    GraphExtensionalCode s a e ↔ InjectiveCode s h := by
  constructor
  · intro hExt x y c hxc hyc
    obtain ⟨hx, hX⟩ := functional_row_contents hh he hxc
    obtain ⟨hy, hY⟩ := functional_row_contents hh he hyc
    exact hExt x hx y hy (fun z _ => (hX z).trans (hY z).symm)
  · intro hInj x hx y hy hrows
    obtain ⟨c, hxc, _⟩ := hh.1.2 x hx
    obtain ⟨d, hyd, _⟩ := hh.1.2 y hy
    have hX := (functional_row_contents hh he hxc).2
    have hY := (functional_row_contents hh he hyd).2
    have hcd : c = d := by
      apply base.extensional
      intro z
      constructor
      · intro hzc
        exact (hY z).mp ((hrows z (hh.2 x c hxc z hzc)).mp ((hX z).mpr hzc))
      · intro hzd
        exact (hX z).mp ((hrows z (hh.2 y d hyd z hzd)).mpr ((hY z).mpr hzd))
    exact hInj x y d (hcd ▸ hxc) hyd

/-- The set-sized injective fixed-part functional realization principle. -/
def FunctionalBoffaCode (s : U → U → Prop) : Prop :=
  ∀ t, TransitiveCode s t → ∀ a h, FunctionalGraphCode s a h →
    InjectiveCode s h → Subset s t a → (∀ x, s x t → CodedRelation s h x x) →
    ∃ g, FunctionalDecorationCode s a h g ∧ InjectiveCode s g ∧
      ∀ x, s x t → CodedRelation s g x x

theorem bafa_iff_functional (base : BaseCollection s) :
    BAFACode s ↔ FunctionalBoffaCode s := by
  constructor
  · intro hB t ht a h hh hi hta hfix
    obtain ⟨e, hG, he⟩ := functional_graph_presentation base hh
    have hExt := (graph_extensional_iff_row_injective base hh he).mpr hi
    have hend := (endExtension_iff_functional_fixed base hh he hta).mpr hfix
    obtain ⟨T, g, _, hg, hgi, _, hgfix⟩ := hB t ht a e hG hExt hend
    exact ⟨g, (decoration_iff_functional hh he).mp hg, hgi, hgfix⟩
  · intro hB t ht a e hG hExt hend
    obtain ⟨h, hh, he⟩ := graph_functional_presentation base hG
    have hi := (graph_extensional_iff_row_injective base hh he).mp hExt
    have hfix := (endExtension_iff_functional_fixed base hh he hend.1).mp hend
    obtain ⟨g, hg, hgi, hgfix⟩ := hB t ht a h hh hi hend.1 hfix
    have hD := (decoration_iff_functional hh he).mpr hg
    obtain ⟨T, hT, hr⟩ := decoration_transitive_range base hD
    exact ⟨T, g, hT, hD, hgi, hr, hgfix⟩

theorem eval_bafaSentence_functional (base : BaseCollection s) :
    Eval s bafaSentence Fin.elim0 ↔ FunctionalBoffaCode s :=
  (eval_bafaSentence s).trans (bafa_iff_functional base)

theorem functional_fixed_parameter_extension_iff (base : BaseCollection s)
    (hF : FunctionalFixedSolvabilityCode s) {t : U} (ht : TransitiveCode s t)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (htB : Subset (internalMember base) (internalCode base t) B) :
    (∃ T, TransitiveCode s T ∧ Subset s t T ∧ internalCode base T = B ∧
      ParameterInjective base T) ↔ InternallyStrongExtensional s t :=
  fixed_solutions_parameter_extension_iff base
    ((fixed_solvability_iff_functional base).mpr hF) ht B hB htB

#print axioms fixed_solvability_iff_functional
#print axioms bafa_iff_functional
#print axioms functional_fixed_parameter_extension_iff
end FullBridge
