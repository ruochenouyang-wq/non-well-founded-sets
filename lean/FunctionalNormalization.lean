import FunctionalPresentation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def TruncatedRowPresentation (s : U → U → Prop) (a e h : U) : Prop :=
  ∀ x y, CodedRelation s e x y ↔ s x a ∧ s y a ∧
    ∃ c, CodedRelation s h x c ∧ s y c

/-- Values may contain objects outside the domain; g only acts on the domain. -/
def UnrestrictedFunctionalFixedCode (s : U → U → Prop) : Prop :=
  ∀ t, TransitiveCode s t → ∀ a h, FunctionCode s a h → Subset s t a →
    (∀ x, s x t → CodedRelation s h x x) →
    ∃ g, FunctionalDecorationCode s a h g ∧ ∀ x, s x t → CodedRelation s g x x

theorem coded_function_domain {a f x y : U} (hf : FunctionCode s a f)
    (hxy : CodedRelation s f x y) : s x a := by
  obtain ⟨p, hp, hpxy⟩ := hxy
  obtain ⟨x', y', hx', hp'⟩ := hf.1 p hp
  obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxy hp'
  exact hx'

theorem truncated_graph_presentation (base : BaseCollection s) (a h : U) :
    ∃ e, GraphCode s a e ∧ TruncatedRowPresentation s a e h := by
  obtain ⟨e, hG, he⟩ := normalized_relation_comprehension base functionalEdgeFormula
    (cons h Fin.elim0) a
  refine ⟨e, hG, ?_⟩
  intro x y
  have hi := he x y
  rw [eval_functionalEdgeFormula] at hi
  exact hi

theorem decoration_iff_truncated_functional {a e h g : U}
    (he : TruncatedRowPresentation s a e h) :
    DecorationCode s a e g ↔ FunctionalDecorationCode s a h g := by
  constructor
  · rintro ⟨hg, hD⟩
    refine ⟨hg, ?_⟩
    intro x hx v hxv w
    rw [hD x hx v hxv w]
    constructor
    · rintro ⟨y, _, hxy, hyg⟩
      obtain ⟨_, _, c, hxc, hyc⟩ := (he x y).mp hxy
      exact ⟨c, y, hxc, hyc, hyg⟩
    · rintro ⟨c, y, hxc, hyc, hyg⟩
      have hy := coded_function_domain hg hyg
      exact ⟨y, hy, (he x y).mpr ⟨hx, hy, c, hxc, hyc⟩, hyg⟩
  · rintro ⟨hg, hD⟩
    refine ⟨hg, ?_⟩
    intro x hx v hxv w
    rw [hD x hx v hxv w]
    constructor
    · rintro ⟨c, y, hxc, hyc, hyg⟩
      have hy := coded_function_domain hg hyg
      exact ⟨y, hy, (he x y).mpr ⟨hx, hy, c, hxc, hyc⟩, hyg⟩
    · rintro ⟨y, _, hxy, hyg⟩
      obtain ⟨_, _, c, hxc, hyc⟩ := (he x y).mp hxy
      exact ⟨c, y, hxc, hyc, hyg⟩

theorem truncated_graph_fixes_parameter {a e h t : U}
    (hh : FunctionCode s a h) (he : TruncatedRowPresentation s a e h)
    (ht : TransitiveCode s t) (hta : Subset s t a)
    (hfix : ∀ x, s x t → CodedRelation s h x x) :
    EndExtensionCode s a e t := by
  refine ⟨hta, ?_⟩
  intro x hx y
  rw [he x y]
  constructor
  · rintro ⟨_, _, c, hxc, hyc⟩
    obtain ⟨v, _, hu⟩ := hh.2 x (hta x hx)
    have hcx := (hu c hxc).trans (hu x (hfix x hx)).symm
    exact hcx ▸ hyc
  · intro hyx
    exact ⟨hta x hx, hta y (ht x hx y hyx), x, hfix x hx, hyx⟩

/-- The same internal function g solves both presentations; all fixed transitive parts survive. -/
theorem functional_normalization (base : BaseCollection s) {a h : U}
    (hh : FunctionCode s a h) :
    ∃ k, FunctionalGraphCode s a k ∧
      (∀ x c d, CodedRelation s h x c → CodedRelation s k x d →
        ∀ y, s y d ↔ s y c ∧ s y a) ∧
      (∀ g, FunctionalDecorationCode s a h g ↔ FunctionalDecorationCode s a k g) ∧
      (∀ t, TransitiveCode s t → Subset s t a →
        (∀ x, s x t → CodedRelation s h x x) →
        ∀ x, s x t → CodedRelation s k x x) := by
  obtain ⟨e, hG, he⟩ := truncated_graph_presentation base a h
  obtain ⟨k, hk, hek⟩ := graph_functional_presentation base hG
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · intro x c d hxc hxd y
    have hx := coded_function_domain hh hxc
    have hd := (functional_row_contents hk hek hxd).2 y
    rw [← hd, he x y]
    constructor
    · rintro ⟨_, hy, c', hxc', hyc'⟩
      obtain ⟨v, _, hu⟩ := hh.2 x hx
      have hcc := (hu c' hxc').trans (hu c hxc).symm
      exact ⟨hcc ▸ hyc', hy⟩
    · rintro ⟨hyc, hy⟩
      exact ⟨hx, hy, c, hxc, hyc⟩
  · intro g
    exact (decoration_iff_truncated_functional he).symm.trans (decoration_iff_functional hk hek)
  · intro t ht hta hfix
    exact (endExtension_iff_functional_fixed base hk hek hta).mp
      (truncated_graph_fixes_parameter hh he ht hta hfix)

theorem fixed_solvability_iff_unrestricted_functional (base : BaseCollection s) :
    FixedGraphSolvabilityCode s ↔ UnrestrictedFunctionalFixedCode s := by
  constructor
  · intro hF t ht a h hh hta hfix
    obtain ⟨k, hk, _, hsol, hfixed⟩ := functional_normalization base hh
    obtain ⟨g, hg, hgf⟩ := (fixed_solvability_iff_functional base).mp hF t ht a k hk hta
      (hfixed t ht hta hfix)
    exact ⟨g, (hsol g).mpr hg, hgf⟩
  · intro hF
    apply (fixed_solvability_iff_functional base).mpr
    intro t ht a h hh hta hfix
    exact hF t ht a h hh.1 hta hfix

theorem eval_fixedSentence_unrestricted_functional (base : BaseCollection s) :
    Eval s fixedGraphSolvabilitySentence Fin.elim0 ↔ UnrestrictedFunctionalFixedCode s :=
  (eval_fixedGraphSolvabilitySentence s).trans (fixed_solvability_iff_unrestricted_functional base)

def UnrestrictedFunctionalSolvabilityCode (s : U → U → Prop) : Prop :=
  ∀ a h, FunctionCode s a h → ∃ g, FunctionalDecorationCode s a h g

def UnrestrictedFunctionalAFACode (s : U → U → Prop) : Prop :=
  ∀ a h, FunctionCode s a h → ∃ g, FunctionalDecorationCode s a h g ∧
    ∀ k, FunctionalDecorationCode s a h k → k = g

theorem solvability_iff_unrestricted_functional (base : BaseCollection s) :
    GraphSolvabilityCode s ↔ UnrestrictedFunctionalSolvabilityCode s := by
  constructor
  · intro hS a h _
    obtain ⟨e, hG, he⟩ := truncated_graph_presentation base a h
    obtain ⟨g, hg⟩ := hS a e hG
    exact ⟨g, (decoration_iff_truncated_functional he).mp hg⟩
  · intro hS a e hG
    obtain ⟨h, hh, he⟩ := graph_functional_presentation base hG
    obtain ⟨g, hg⟩ := hS a h hh.1
    exact ⟨g, (decoration_iff_functional hh he).mpr hg⟩

theorem afa_iff_unrestricted_functional (base : BaseCollection s) :
    AFACode s ↔ UnrestrictedFunctionalAFACode s := by
  constructor
  · intro hA a h _
    obtain ⟨e, hG, he⟩ := truncated_graph_presentation base a h
    obtain ⟨g, hg, hu⟩ := hA a e hG
    exact ⟨g, (decoration_iff_truncated_functional he).mp hg,
      fun k hk => hu k ((decoration_iff_truncated_functional he).mpr hk)⟩
  · intro hA a e hG
    obtain ⟨h, hh, he⟩ := graph_functional_presentation base hG
    obtain ⟨g, hg, hu⟩ := hA a h hh.1
    exact ⟨g, (decoration_iff_functional hh he).mpr hg,
      fun k hk => hu k ((decoration_iff_functional hh he).mp hk)⟩

theorem eval_solvabilitySentence_unrestricted_functional (base : BaseCollection s) :
    Eval s graphSolvabilitySentence Fin.elim0 ↔ UnrestrictedFunctionalSolvabilityCode s :=
  (eval_graphSolvabilitySentence s).trans (solvability_iff_unrestricted_functional base)

theorem eval_afaSentence_unrestricted_functional (base : BaseCollection s) :
    Eval s afaSentence Fin.elim0 ↔ UnrestrictedFunctionalAFACode s :=
  (eval_afaSentence s).trans (afa_iff_unrestricted_functional base)

#print axioms functional_normalization
#print axioms fixed_solvability_iff_unrestricted_functional
#print axioms afa_iff_unrestricted_functional
end FullBridge
