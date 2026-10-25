import PrunedCodeTransfer
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def prunedClassPullbackFormula : Formula 5 :=
  .conj (.member 1 2) (.ex (.conj (graphClassFormula 0 2 3 4) (relatedFormula 5 0 1)))

theorem eval_prunedClassPullbackFormula (a m f x v : U) :
    Eval s prunedClassPullbackFormula (cons v (cons x (cons a (cons m (cons f Fin.elim0))))) ↔
      s x a ∧ ∃ c, GraphClassCode s a m x c ∧ CodedRelation s f c v := by
  simp only [prunedClassPullbackFormula, Eval, eval_graphClassFormula, eval_relatedFormula]
  rfl

theorem pruned_class_pullback_function (base : BaseCollection s) {b : U} {A : PrunedQuotient base b}
    (P : PrunedNodePresentation base b A) {f : U} (hf : FunctionCode s P.nodes f) :
    ∃ g, FunctionCode s P.representatives g ∧ ∀ x v, CodedRelation s g x v ↔
      s x P.representatives ∧ ∃ c, GraphClassCode s P.representatives P.relation x c ∧ CodedRelation s f c v := by
  obtain ⟨d, hd⟩ := codedRelation_component_bound base.union f
  obtain ⟨u, hu⟩ := binary_union_exists base.pairing base.union P.representatives d
  obtain ⟨g, hgmem⟩ := relation_comprehension_members base prunedClassPullbackFormula
    (cons P.representatives (cons P.relation (cons f Fin.elim0))) u
  have hg' : ∀ x v, CodedRelation s g x v ↔ s x P.representatives ∧
      ∃ c, GraphClassCode s P.representatives P.relation x c ∧ CodedRelation s f c v := by
    intro x v
    constructor
    · rintro ⟨p, hp, hpxv⟩
      obtain ⟨x', v', _, _, hp', hev⟩ := (hgmem p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxv hp'
      exact (eval_prunedClassPullbackFormula _ _ _ x v).mp hev
    · rintro ⟨hx, c, hxc, hcv⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x v
      exact ⟨p, (hgmem p).mpr ⟨x, v, (hu x).mpr (Or.inl hx), (hu v).mpr (Or.inr (hd c v hcv).2),
        hp, (eval_prunedClassPullbackFormula _ _ _ x v).mpr ⟨hx, c, hxc, hcv⟩⟩, hp⟩
  refine ⟨g, ⟨?_, ?_⟩, hg'⟩
  · intro p hp
    obtain ⟨x, v, _, _, hpv, hev⟩ := (hgmem p).mp hp
    exact ⟨x, v, ((eval_prunedClassPullbackFormula _ _ _ x v).mp hev).1, hpv⟩
  · intro x hx
    obtain ⟨c, hc⟩ := graph_class_exists base P.representatives P.relation x
    obtain ⟨v, hcv, _⟩ := hf.2 c ((P.nodes_iff c).mpr ⟨x, hx, hc⟩)
    refine ⟨v, (hg' x v).mpr ⟨hx, c, hc, hcv⟩, ?_⟩
    intro w hxw
    obtain ⟨_, c', hc', hc'w⟩ := (hg' x w).mp hxw
    have hcc := graph_class_unique base hc' hc
    subst c'
    exact coded_function_value_unique hf hc'w hcv

/-- Every target-coded extensional graph has an actual target-coded injective
    decoration. Preserving a prescribed fixed target part is not asserted here. -/
theorem pruned_target_extensional_realization (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) {b : U} (hb : SelfSingleton s b) :
    ExtensionalRealizationCode (prunedMember base b) := by
  intro A R _hG hExt
  have hbb := (hb b).mpr rfl
  obtain ⟨P, e, heG, heExt, he⟩ := pruned_target_extensional_graph_lift base hbb A R hExt
  obtain ⟨f, T, hf, _, hT, hTgood, hTtrans, hfembed⟩ :=
    pruned_extensional_source_graph_embedding base hF hb heG heExt
  obtain ⟨g, hg, hgp⟩ := pruned_class_pullback_function base P hf
  have hgGood : ∀ x v, CodedRelation s g x v → ¬s b v := by
    intro x v hxv
    obtain ⟨_, c, _, hcv⟩ := (hgp x v).mp hxv
    exact hTgood v ((hT v).mpr ⟨c, coded_function_domain hf hcv, hcv⟩)
  have hgCoh : ∀ x y v w, CodedRelation s g x v → CodedRelation s g y w →
      prunedCode base b x = prunedCode base b y → prunedCode base b v = prunedCode base b w := by
    intro x y v w hxv hyw hxy
    obtain ⟨hx, c, hc, hcv⟩ := (hgp x v).mp hxv
    obtain ⟨hy, d, hd, hdw⟩ := (hgp y w).mp hyw
    exact (hfembed c d v w hcv hdw).1.mpr ((pruned_node_class_eq base P hx hy hc hd).mpr hxy)
  have hgReflect : ∀ x y v w, CodedRelation s g x v → CodedRelation s g y w →
      prunedCode base b v = prunedCode base b w → prunedCode base b x = prunedCode base b y := by
    intro x y v w hxv hyw hvw
    obtain ⟨hx, c, hc, hcv⟩ := (hgp x v).mp hxv
    obtain ⟨hy, d, hd, hdw⟩ := (hgp y w).mp hyw
    exact (pruned_node_class_eq base P hx hy hc hd).mp ((hfembed c d v w hcv hdw).1.mp hvw)
  have hgQ0 := pruned_function_forward base hbb hg P.clean hgGood hgCoh
  have hgQ : FunctionCode (prunedMember base b) A (prunedCode base b g) := by
    simpa only [P.image] using hgQ0
  have hgI := pruned_function_injective base hbb hg P.clean hgGood hgReflect
  have hgRel := pruned_coded_relation_image base hbb (pruned_function_retained hg P.clean hgGood)
  refine ⟨prunedCode base b g, ⟨hgQ, ?_⟩, hgI⟩
  intro X _hX V hXV W
  obtain ⟨x, v, hxv, hqx, hqv⟩ := (hgRel X V).mp hXV
  obtain ⟨hx, c, hc, hcv⟩ := (hgp x v).mp hxv
  have hcX : PrunedNodeCorresponds P c X := ⟨x, hx, hc, hqx⟩
  have hvT : prunedMember base b V (prunedCode base b T) :=
    ((pruned_good_row base hbb hTgood).2 V).mpr
      ⟨v, (hT v).mpr ⟨c, coded_function_domain hf hcv, hcv⟩, hqv⟩
  constructor
  · intro hWV
    have hWT := hTtrans V hvT W hWV
    obtain ⟨w, hwT, hqw⟩ := ((pruned_good_row base hbb hTgood).2 W).mp hWT
    obtain ⟨d, hd, hdw⟩ := (hT w).mp hwT
    obtain ⟨Y, hYA, hdY⟩ := (pruned_node_correspondence_total base hbb P).1 d hd
    have hqwv : prunedMember base b (prunedCode base b w) (prunedCode base b v) := by
      simpa only [hqw, hqv] using hWV
    have hcd := (hfembed c d v w hcv hdw).2.mp hqwv
    refine ⟨Y, hYA, (he c d X Y hcX hdY).mp hcd, ?_⟩
    obtain ⟨y, hy, hyd, hqy⟩ := hdY
    exact (hgRel Y W).mpr ⟨y, w, (hgp y w).mpr ⟨hy, d, hyd, hdw⟩, hqy, hqw⟩
  · rintro ⟨Y, hYA, hXY, hYW⟩
    obtain ⟨d, hd, hdY⟩ := (pruned_node_correspondence_total base hbb P).2 Y hYA
    obtain ⟨w, hdw, _⟩ := hf.2 d hd
    have hcd := (he c d X Y hcX hdY).mpr hXY
    have hqwV : prunedMember base b (prunedCode base b w) V := by
      have h := (hfembed c d v w hcv hdw).2.mpr hcd
      simpa only [hqv] using h
    obtain ⟨y, hy, hyd, hqy⟩ := hdY
    have hYw := (hgRel Y (prunedCode base b w)).mpr
      ⟨y, w, (hgp y w).mpr ⟨hy, d, hyd, hdw⟩, hqy, rfl⟩
    have hWw := coded_function_value_unique hgQ hYW hYw
    exact hWw.symm ▸ hqwV

theorem afa_source_pruned_extensional_realization (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hb : SelfSingleton s b) : ExtensionalRealizationCode (prunedMember base b) :=
  pruned_target_extensional_realization base (afa_fixed_graph_solvability base hA) hb

#print axioms pruned_target_extensional_realization
end FullBridge
