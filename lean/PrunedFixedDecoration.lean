import PrunedJointRealization
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A total source relation may become a function after quotienting, even when
    it has several source values; coherence is proved, not assumed as Choice. -/
theorem pruned_relational_function (base : BaseCollection s) {b a r : U} (hbb : s b b)
    (hpairs : ∀ p, s p r → ∃ x v, s x a ∧ IsOrderedPair s p x v)
    (htotal : ∀ x, s x a → ∃ v, CodedRelation s r x v)
    (ha : ∀ x, s x a → ¬s b x)
    (hv : ∀ x v, CodedRelation s r x v → ¬s b v)
    (hcoh : ∀ x y v w, CodedRelation s r x v → CodedRelation s r y w →
      prunedCode base b x = prunedCode base b y → prunedCode base b v = prunedCode base b w) :
    FunctionCode (prunedMember base b) (prunedCode base b a) (prunedCode base b r) := by
  have hr : RetainedRelationCode s b r := by
    intro p hp
    obtain ⟨x, v, hx, hxv⟩ := hpairs p hp
    exact ⟨x, v, ha x hx, hv x v ⟨p, hp, hxv⟩, hxv⟩
  have hg := retained_relation_members base hbb hr
  constructor
  · intro P hP
    obtain ⟨p, hp, rfl⟩ := ((pruned_good_row base hbb hg).2 P).mp hP
    obtain ⟨x, v, hx, hpv⟩ := hpairs p hp
    exact ⟨prunedCode base b x, prunedCode base b v,
      ((pruned_good_row base hbb ha).2 _).mpr ⟨x, hx, rfl⟩,
      (pruned_orderedPair_forward base hbb (ha x hx) (hv x v ⟨p, hp, hpv⟩) hpv).2⟩
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := ((pruned_good_row base hbb ha).2 X).mp hX
    obtain ⟨v, hxv⟩ := htotal x hx
    refine ⟨prunedCode base b v, (pruned_coded_relation_image base hbb hr _ _).mpr ⟨x, v, hxv, rfl, rfl⟩, ?_⟩
    intro Y hY
    obtain ⟨y, w, hyw, hqy, hqw⟩ := (pruned_coded_relation_image base hbb hr _ _).mp hY
    exact hqw.symm.trans (hcoh y x w v hyw hxv hqy)

def jointPullbackFormula : Formula 5 :=
  .conj (.member 1 2) (.ex (.conj (graphClassFormula 0 2 3 4) (relatedFormula 5 1 0)))

theorem eval_jointPullbackFormula (a m j x v : U) :
    Eval s jointPullbackFormula (cons v (cons x (cons a (cons m (cons j Fin.elim0))))) ↔
      s x a ∧ ∃ c, GraphClassCode s a m x c ∧ CodedRelation s j v c := by
  simp only [jointPullbackFormula, Eval, eval_graphClassFormula, eval_relatedFormula]
  rfl

/-- Actual relational pullback: repeated old representatives are retained. -/
theorem pruned_joint_pullback_relation (base : BaseCollection s) {b : U}
    {A : PrunedQuotient base b} (P : PrunedNodePresentation base b A) {e : U}
    (J : PrunedJointRealization base b P e) :
    ∃ g, (∀ p, s p g → ∃ x v, s x P.representatives ∧ IsOrderedPair s p x v) ∧
      ∀ x v, CodedRelation s g x v ↔ s x P.representatives ∧
        ∃ c, GraphClassCode s P.representatives P.relation x c ∧ CodedRelation s J.classifier v c := by
  obtain ⟨u, hu⟩ := binary_union_exists base.pairing base.union P.representatives J.carrier
  obtain ⟨g, hmem⟩ := relation_comprehension_members base jointPullbackFormula
    (cons P.representatives (cons P.relation (cons J.classifier Fin.elim0))) u
  refine ⟨g, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, v, _, _, hpv, hev⟩ := (hmem p).mp hp
    exact ⟨x, v, ((eval_jointPullbackFormula _ _ _ x v).mp hev).1, hpv⟩
  · intro x v
    constructor
    · rintro ⟨p, hp, hpv⟩
      obtain ⟨x', v', _, _, hpv', hev⟩ := (hmem p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpv hpv'
      exact (eval_jointPullbackFormula _ _ _ x v).mp hev
    · rintro ⟨hx, c, hxc, hvc⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x v
      exact ⟨p, (hmem p).mpr ⟨x, v, (hu x).mpr (Or.inl hx),
        (hu v).mpr (Or.inr (coded_function_domain J.function hvc)), hp,
        (eval_jointPullbackFormula _ _ _ x v).mpr ⟨hx, c, hxc, hvc⟩⟩, hp⟩

/-- The actual quotient of the relational pullback is a single-valued injective
    decoration and fixes each target object represented by its own image. -/
theorem pruned_joint_fixed_decoration (base : BaseCollection s) {b : U} (hbb : s b b)
    {T A R : PrunedQuotient base b} (P : PrunedNodePresentation base b A) {e : U}
    (he : ∀ c d X Y, PrunedNodeCorresponds P c X → PrunedNodeCorresponds P d Y →
      (CodedRelation s e c d ↔ CodedRelation (prunedMember base b) R X Y))
    (J : PrunedJointRealization base b P e)
    (hfixed : ∀ X, prunedMember base b X T → ∃ v c,
      prunedCode base b v = X ∧ CodedRelation s J.classifier v c ∧ PrunedNodeCorresponds P c X) :
    ∃ F, DecorationCode (prunedMember base b) A R F ∧ InjectiveCode (prunedMember base b) F ∧
      ∀ X, prunedMember base b X T → CodedRelation (prunedMember base b) F X X := by
  obtain ⟨g, hpairs, hg⟩ := pruned_joint_pullback_relation base P J
  have htotal : ∀ x, s x P.representatives → ∃ v, CodedRelation s g x v := by
    intro x hx
    obtain ⟨c, hc⟩ := graph_class_exists base P.representatives P.relation x
    obtain ⟨v, hvc⟩ := J.onto c ((P.nodes_iff c).mpr ⟨x, hx, hc⟩)
    exact ⟨v, (hg x v).mpr ⟨hx, c, hc, hvc⟩⟩
  have hgood : ∀ x v, CodedRelation s g x v → ¬s b v := by
    intro x v hxv
    obtain ⟨_, c, _, hvc⟩ := (hg x v).mp hxv
    exact J.retained v (coded_function_domain J.function hvc)
  have hcoh : ∀ x y v w, CodedRelation s g x v → CodedRelation s g y w →
      (prunedCode base b x = prunedCode base b y ↔ prunedCode base b v = prunedCode base b w) := by
    intro x y v w hxv hyw
    obtain ⟨hx, c, hxc, hvc⟩ := (hg x v).mp hxv
    obtain ⟨hy, d, hyd, hwd⟩ := (hg y w).mp hyw
    exact (pruned_node_class_eq base P hx hy hxc hyd).symm.trans (J.kernel v w c d hvc hwd)
  have hQ0 := pruned_relational_function base hbb hpairs htotal P.clean hgood
    (fun x y v w hxv hyw => (hcoh x y v w hxv hyw).mp)
  have hQ : FunctionCode (prunedMember base b) A (prunedCode base b g) := by
    simpa only [P.image] using hQ0
  have hret : RetainedRelationCode s b g := by
    intro p hp
    obtain ⟨x, v, hx, hpv⟩ := hpairs p hp
    exact ⟨x, v, P.clean x hx, hgood x v ⟨p, hp, hpv⟩, hpv⟩
  have hRel := pruned_coded_relation_image base hbb hret
  have hInjective : InjectiveCode (prunedMember base b) (prunedCode base b g) := by
    intro X Y V hXV hYV
    obtain ⟨x, v, hxv, hqx, hqv⟩ := (hRel X V).mp hXV
    obtain ⟨y, w, hyw, hqy, hqw⟩ := (hRel Y V).mp hYV
    exact hqx.symm.trans (((hcoh x y v w hxv hyw).mpr (hqv.trans hqw.symm)).trans hqy)
  refine ⟨prunedCode base b g, ⟨hQ, ?_⟩, hInjective, ?_⟩
  · intro X _ V hXV W
    obtain ⟨x, v, hxv, hqx, hqv⟩ := (hRel X V).mp hXV
    obtain ⟨hx, c, hxc, hvc⟩ := (hg x v).mp hxv
    have hcX : PrunedNodeCorresponds P c X := ⟨x, hx, hxc, hqx⟩
    have hvC := coded_function_domain J.function hvc
    constructor
    · intro hWV
      have hWv : prunedMember base b W (prunedCode base b v) := hqv.symm ▸ hWV
      obtain ⟨w, hvw, hqw⟩ := (least_global_exact_members base prunedMemberFormula
        (cons b Fin.elim0) (pruned_edges_are_members b) v W).mp hWv
      obtain ⟨d, hwd, _⟩ := J.function.2 w (J.closed v hvC w hvw)
      obtain ⟨Y, hYA, hdY⟩ := (pruned_node_correspondence_total base hbb P).1 d (J.range w d hwd)
      have hcd := (J.rows v c hvC hvc d (J.range w d hwd)).mpr ⟨w, hvw, hwd⟩
      refine ⟨Y, hYA, (he c d X Y hcX hdY).mp hcd, ?_⟩
      obtain ⟨y, hy, hyd, hqy⟩ := hdY
      exact (hRel Y W).mpr ⟨y, w, (hg y w).mpr ⟨hy, d, hyd, hwd⟩, hqy, hqw⟩
    · rintro ⟨Y, _, hXY, hYW⟩
      obtain ⟨y, w, hyw, hqy, hqw⟩ := (hRel Y W).mp hYW
      obtain ⟨hy, d, hyd, hwd⟩ := (hg y w).mp hyw
      have hdY : PrunedNodeCorresponds P d Y := ⟨y, hy, hyd, hqy⟩
      have hcd := (he c d X Y hcX hdY).mpr hXY
      obtain ⟨w', hvw', hw'd⟩ := (J.rows v c hvC hvc d (J.range w d hwd)).mp hcd
      have hqww := (J.kernel w' w d d hw'd hwd).mp rfl
      have hWv : prunedMember base b W (prunedCode base b v) :=
        (least_global_exact_members base prunedMemberFormula (cons b Fin.elim0)
          (pruned_edges_are_members b) v W).mpr ⟨w', hvw', hqww.trans hqw⟩
      exact hqv ▸ hWv
  · intro X hXT
    obtain ⟨v, c, hqv, hvc, x, hx, hxc, hqx⟩ := hfixed X hXT
    exact (hRel X X).mpr ⟨x, v, (hg x v).mpr ⟨hx, c, hxc, hvc⟩, hqx, hqv⟩

/-- Full BAFA, with its prescribed transitive part and actual coded decoration. -/
theorem pruned_quotient_bafa (base : BaseCollection s) (hF : FixedGraphSolvabilityCode s)
    {b : U} (hb : SelfSingleton s b) : BAFACode (prunedMember base b) := by
  intro T hT A R _hG hExt hend
  have hbb := (hb b).mpr rfl
  obtain ⟨P, e, _, heExt, he⟩ := pruned_target_extensional_graph_lift base hbb A R hExt
  obtain ⟨J, hfixed⟩ := pruned_fixed_joint_realization base hF hb hT P he heExt hend
  obtain ⟨F, hDec, hInj, hFix⟩ := pruned_joint_fixed_decoration base hbb P he J hfixed
  obtain ⟨V, hTrans, hRange⟩ := decoration_transitive_range (pruned_quotient_base base hbb) hDec
  exact ⟨V, F, hTrans, hDec, hInj, hRange, hFix⟩

theorem afa_source_pruned_bafa (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hb : SelfSingleton s b) : BAFACode (prunedMember base b) :=
  pruned_quotient_bafa base (afa_fixed_graph_solvability base hA) hb

#print axioms pruned_quotient_bafa
#print axioms afa_source_pruned_bafa
end FullBridge
