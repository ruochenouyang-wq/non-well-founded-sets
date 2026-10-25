import CanonicalGraphEvaluation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

noncomputable def prunedEvaluationMap (base : BaseCollection s) (hA : AFACode s) (b : U) :
    PrunedQuotient base b → U :=
  Quotient.lift (canonicalGraphValue base hA prunedMemberFormula (cons b Fin.elim0))
    (fun _ _ h => canonical_graph_value_respects_least base hA prunedMemberFormula
      (cons b Fin.elim0) (pruned_edges_are_members b) h)

theorem pruned_evaluation_code (base : BaseCollection s) (hA : AFACode s) (b x : U) :
    prunedEvaluationMap base hA b (prunedCode base b x) =
      canonicalGraphValue base hA prunedMemberFormula (cons b Fin.elim0) x := rfl

/-- Exact image of member rows; neither injectivity nor reflection of individual
    edges between chosen preimages is asserted. -/
theorem pruned_evaluation_exact_members (base : BaseCollection s) (hA : AFACode s) (b : U) :
    ExactMembers (prunedMember base b) s (prunedEvaluationMap base hA b) := by
  intro X z
  refine Quotient.inductionOn X ?_
  intro x
  change s z (canonicalGraphValue base hA prunedMemberFormula (cons b Fin.elim0) x) ↔ _
  refine (canonical_graph_value_rows base hA prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) x z).trans ⟨?_, ?_⟩
  · rintro ⟨y, hxy, hyz⟩
    exact ⟨prunedCode base b y, (least_global_exact_members base prunedMemberFormula
      (cons b Fin.elim0) (pruned_edges_are_members b) x _).mpr ⟨y, hxy, rfl⟩, hyz⟩
  · rintro ⟨Y, hYX, hYz⟩
    obtain ⟨y, hxy, hqy⟩ := (least_global_exact_members base prunedMemberFormula
      (cons b Fin.elim0) (pruned_edges_are_members b) x Y).mp hYX
    exact ⟨y, hxy, (congrArg (prunedEvaluationMap base hA b) hqy).trans hYz⟩

/-- Composition is represented by an actual normalized source function graph. -/
theorem coded_functions_compose (base : BaseCollection s) {a b f g : U}
    (hf : FunctionCode s a f) (hg : FunctionCode s b g)
    (hrange : ∀ x y, CodedRelation s f x y → s y b) :
    ∃ k, FunctionCode s a k ∧ ∀ x z, CodedRelation s k x z ↔
      ∃ y, CodedRelation s f x y ∧ CodedRelation s g y z := by
  obtain ⟨d, hd⟩ := codedRelation_component_bound base.union g
  obtain ⟨u, hu⟩ := binary_union_exists base.pairing base.union a d
  obtain ⟨k, hmem⟩ := relation_comprehension_members base compositionFormula (cons f (cons g Fin.elim0)) u
  have hk : ∀ x z, CodedRelation s k x z ↔ ∃ y, CodedRelation s f x y ∧ CodedRelation s g y z := by
    intro x z
    constructor
    · rintro ⟨p, hp, hpxz⟩
      obtain ⟨x', z', _, _, hp', hev⟩ := (hmem p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxz hp'
      exact (eval_compositionFormula x z f g).mp hev
    · rintro ⟨y, hxy, hyz⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x z
      exact ⟨p, (hmem p).mpr ⟨x, z, (hu x).mpr (Or.inl (coded_function_domain hf hxy)),
        (hu z).mpr (Or.inr (hd y z hyz).2), hp, (eval_compositionFormula x z f g).mpr ⟨y, hxy, hyz⟩⟩, hp⟩
  refine ⟨k, ⟨?_, ?_⟩, hk⟩
  · intro p hp
    obtain ⟨x, z, _, _, hpxz, hev⟩ := (hmem p).mp hp
    obtain ⟨y, hxy, _⟩ := (eval_compositionFormula x z f g).mp hev
    exact ⟨x, z, coded_function_domain hf hxy, hpxz⟩
  · intro x hx
    obtain ⟨y, hxy, _⟩ := hf.2 x hx
    obtain ⟨z, hyz, _⟩ := hg.2 y (hrange x y hxy)
    refine ⟨z, (hk x z).mpr ⟨y, hxy, hyz⟩, ?_⟩
    intro w hxw
    obtain ⟨y', hxy', hy'w⟩ := (hk x w).mp hxw
    have heq := coded_function_value_unique hf hxy' hxy
    subst y'
    exact coded_function_value_unique hg hy'w hyz

/-- Tagged realizations of ordinary source membership graphs show that every
    original AFA object is the evaluation of an actual pruned-quotient object. -/
theorem pruned_evaluation_surjective (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hb : SelfSingleton s b) :
    ∀ z, ∃ X, prunedEvaluationMap base hA b X = z := by
  intro z
  obtain ⟨c, hc, hzc⟩ := transitive_sets_cover base z
  obtain ⟨e, i, hG, hi, he, hir⟩ := membership_graph_identity_decoration base hc
  obtain ⟨f, V, hf, _, hV, _, hrows⟩ :=
    pruned_source_graph_realization base (afa_fixed_graph_solvability base hA) hb hG
  obtain ⟨k, hk, hkr⟩ := canonical_graph_value_function base hA prunedMemberFormula
    (cons b Fin.elim0) (pruned_edges_are_members b) V
  have hin : ∀ x v, CodedRelation s f x v → s v V :=
    fun x v hxv => (hV v).mpr ⟨x, coded_function_domain hf hxv, hxv⟩
  obtain ⟨g, hg, hgr⟩ := coded_functions_compose base hf hk hin
  have hgDec : DecorationCode s c e g := by
    refine ⟨hg, ?_⟩
    intro x hx v hxv w
    obtain ⟨u, hxu, huv⟩ := (hgr x v).mp hxv
    have hdu := ((hkr u v).mp huv).2
    have hrow := canonical_graph_value_rows base hA prunedMemberFormula (cons b Fin.elim0)
      (pruned_edges_are_members b) u w
    rw [hdu] at hrow
    refine hrow.trans ⟨?_, ?_⟩
    · rintro ⟨u', huu', hdu'⟩
      obtain ⟨y, hy, hxy, hyu'⟩ := (hrows x u hx hxu u').mp huu'
      exact ⟨y, hy, hxy, (hgr y w).mpr ⟨u', hyu', (hkr u' w).mpr ⟨hin y u' hyu', hdu'⟩⟩⟩
    · rintro ⟨y, hy, hxy, hyw⟩
      obtain ⟨u', hyu', hu'w⟩ := (hgr y w).mp hyw
      exact ⟨u', (hrows x u hx hxu u').mpr ⟨y, hy, hxy, hyu'⟩, ((hkr u' w).mp hu'w).2⟩
  obtain ⟨l, _, hlu⟩ := hA c e hG
  have hgi : g = i := (hlu g hgDec).trans (hlu i hi).symm
  obtain ⟨u, hzu, _⟩ := hf.2 z hzc
  have hgzd : CodedRelation s g z (canonicalGraphValue base hA prunedMemberFormula (cons b Fin.elim0) u) :=
    (hgr z _).mpr ⟨u, hzu, (hkr u _).mpr ⟨hin z u hzu, rfl⟩⟩
  refine ⟨prunedCode base b u, ?_⟩
  exact ((hir z _).mp (hgi ▸ hgzd)).2

theorem exact_members_preserves_selfSingleton {V : Type u} {t : V → V → Prop}
    {q : U → V} (hm : ExactMembers s t q) {a : U} (ha : SelfSingleton s a) :
    SelfSingleton t (q a) := by
  intro z
  refine (hm a z).trans ⟨?_, ?_⟩
  · rintro ⟨x, hx, hqx⟩
    have hxa := (ha x).mp hx
    exact hqx.symm.trans (congrArg q hxa)
  · intro hz
    exact ⟨a, (ha a).mpr rfl, hz.symm⟩

/-- The first comparison is necessarily noninjective: its two distinct target
    self-singletons evaluate to the unique source AFA self-singleton. -/
theorem pruned_evaluation_distinct_equal_values (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hb : SelfSingleton s b) :
    ∃ X Y, X ≠ Y ∧ prunedEvaluationMap base hA b X = prunedEvaluationMap base hA b Y := by
  obtain ⟨X, Y, hne, hX, hY⟩ := pruned_distinct_selfSingletons base
    (afa_fixed_graph_solvability base hA) hb
  have hm := pruned_evaluation_exact_members base hA b
  exact ⟨X, Y, hne, afa_selfSingleton_unique base hA
    (exact_members_preserves_selfSingleton hm hX) (exact_members_preserves_selfSingleton hm hY)⟩

#print axioms pruned_evaluation_exact_members
#print axioms pruned_evaluation_surjective
#print axioms pruned_evaluation_distinct_equal_values
end FullBridge
