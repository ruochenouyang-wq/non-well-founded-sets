import PrunedFixedCover
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Solve new-node equations with an arbitrary coded boundary relation into a
    fixed transitive source part. Boundary rows need not be singletons. -/
theorem boundary_graph_solution_exists (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) {a e t labels : U}
    (hG : GraphCode s a e) (ht : TransitiveCode s t)
    (hBoundary : ∀ x l, CodedRelation s labels x l → s x a ∧ s l t) : ∃ f, TaggedDecorationCode s a e labels f := by
  obtain ⟨c, k, hkF, hkI, hkR, hkFresh⟩ := fresh_parameter_copy base a t
  have hkC : ∀ x z, CodedRelation s k x z → s z c :=
    fun x z h => (hkR z).mpr ⟨x, coded_function_domain hkF h, h⟩
  have hlT : ∀ x l, CodedRelation s labels x l → s l t :=
    fun x l h => (hBoundary x l h).2
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union t c
  have htd : Subset s t d := fun x hx => (hd x).mpr (Or.inl hx)
  have hcd : Subset s c d := fun x hx => (hd x).mpr (Or.inr hx)
  obtain ⟨E, hEG, hE⟩ := normalized_relation_comprehension base copiedTaggedEdgeFormula
    (cons t (cons e (cons k (cons labels Fin.elim0)))) d
  have hE' : ∀ x y, CodedRelation s E x y ↔ CopiedTaggedEdge s t e k labels x y := by
    intro x y
    have h := hE x y
    rw [eval_copiedTaggedEdgeFormula] at h
    refine h.trans ⟨fun h => h.2.2, ?_⟩
    intro hxy
    refine ⟨?_, ?_, hxy⟩
    · rcases hxy with h | ⟨z, hz, _⟩
      · exact htd x h.1
      · exact hcd x (hkC z x hz)
    · rcases hxy with h | ⟨z, _, h⟩
      · exact htd y (ht x h.1 y h.2)
      · rcases h with ⟨w, _, hwy⟩ | hzy
        · exact hcd y (hkC w y hwy)
        · exact htd y (hlT z y hzy)
  have hend : EndExtensionCode s d E t := by
    refine ⟨htd, ?_⟩
    intro x hx y
    refine (hE' x y).trans ⟨?_, fun h => Or.inl ⟨hx, h⟩⟩
    intro h
    rcases h with h | ⟨z, hz, _⟩
    · exact h.2
    · exact False.elim (hkFresh x (hkC z x hz) hx)
  obtain ⟨g, hg, hfix⟩ := hF t ht d E hEG hend
  obtain ⟨bound, hbound⟩ := codedRelation_component_bound base.union g
  obtain ⟨u, hu⟩ := binary_union_exists base.pairing base.union a bound
  obtain ⟨f, hfmem⟩ := relation_comprehension_members base compositionFormula
    (cons k (cons g Fin.elim0)) u
  have hf' : ∀ x v, CodedRelation s f x v ↔ ∃ z, CodedRelation s k x z ∧ CodedRelation s g z v := by
    intro x v
    constructor
    · rintro ⟨p, hp, hpxv⟩
      obtain ⟨x', v', _, _, hp', hev⟩ := (hfmem p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxv hp'
      exact (eval_compositionFormula x v k g).mp hev
    · rintro ⟨z, hxz, hzv⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x v
      exact ⟨p, (hfmem p).mpr ⟨x, v, (hu x).mpr (Or.inl (coded_function_domain hkF hxz)),
        (hu v).mpr (Or.inr (hbound z v hzv).2), hp,
        (eval_compositionFormula x v k g).mpr ⟨z, hxz, hzv⟩⟩, hp⟩
  have hfF : FunctionCode s a f := by
    constructor
    · intro p hp
      obtain ⟨x, v, _, _, hpair, hev⟩ := (hfmem p).mp hp
      obtain ⟨z, hxz, _⟩ := (eval_compositionFormula x v k g).mp hev
      exact ⟨x, v, coded_function_domain hkF hxz, hpair⟩
    · intro x hx
      obtain ⟨z, hxz, _⟩ := hkF.2 x hx
      obtain ⟨v, hzv, _⟩ := hg.1.2 z (hcd z (hkC x z hxz))
      refine ⟨v, (hf' x v).mpr ⟨z, hxz, hzv⟩, ?_⟩
      intro w hw
      obtain ⟨z', hxz', hz'w⟩ := (hf' x w).mp hw
      have hzz := coded_function_value_unique hkF hxz' hxz
      subst z'
      exact coded_function_value_unique hg.1 hz'w hzv
  refine ⟨f, hfF, ?_⟩
  intro x hx v hxv w
  obtain ⟨z, hxz, hzv⟩ := (hf' x v).mp hxv
  have hzd := hcd z (hkC x z hxz)
  have hzt := hkFresh z (hkC x z hxz)
  constructor
  · intro hwv
    obtain ⟨u', _, hzu, huw⟩ := (hg.2 z hzd v hzv w).mp hwv
    rcases (hE' z u').mp hzu with h | ⟨x', hx'z, h⟩
    · exact False.elim (hzt h.1)
    · have hxx := hkI x' x z hx'z hxz
      subst x'
      rcases h with ⟨y, hxy, hyu⟩ | hxu
      · exact Or.inl ⟨y, (graphCode_endpoints hG hxy).2, hxy, (hf' y w).mpr ⟨u', hyu, huw⟩⟩
      · have hwu := coded_function_value_unique hg.1 huw (hfix u' (hlT x u' hxu))
        exact Or.inr (hwu.symm ▸ hxu)
  · intro hw
    rcases hw with ⟨y, _, hxy, hyw⟩ | hxw
    · obtain ⟨u', hyu, huw⟩ := (hf' y w).mp hyw
      exact (hg.2 z hzd v hzv w).mpr ⟨u', hcd u' (hkC y u' hyu),
        (hE' z u').mpr (Or.inr ⟨x, hxz, Or.inl ⟨y, hxy, hyu⟩⟩), huw⟩
    · exact (hg.2 z hzd v hzv w).mpr ⟨w, htd w (hlT x w hxw),
        (hE' z w).mpr (Or.inr ⟨x, hxz, Or.inr hxw⟩), hfix w (hlT x w hxw)⟩



def MixedTaggedDecorationCode (s : U → U → Prop) (a e S h labels f : U) : Prop :=
  FunctionCode s a f ∧ ∀ x, s x a → ∀ v, CodedRelation s f x v → ∀ w,
    s w v ↔ (∃ y, s y a ∧ CodedRelation s e x y ∧ CodedRelation s f y w) ∨
      (s w S ∧ ∃ d, CodedRelation s h w d ∧ CodedRelation s e x d) ∨
      CodedRelation s labels x w

def mixedBoundaryFormula : Formula 7 :=
  .conj (.member 1 2)
    ((Formula.conj (.member 0 3) (.ex (.conj (relatedFormula 5 1 0) (relatedFormula 6 2 0)))).disj
      (relatedFormula 6 1 0))

theorem eval_mixedBoundaryFormula (a S h e labels x y : U) :
    Eval s mixedBoundaryFormula
      (cons y (cons x (cons a (cons S (cons h (cons e (cons labels Fin.elim0))))))) ↔
    s x a ∧ ((s y S ∧ ∃ d, CodedRelation s h y d ∧ CodedRelation s e x d) ∨
      CodedRelation s labels x y) := by
  simp only [mixedBoundaryFormula, Eval, eval_disj, eval_relatedFormula]
  rfl

/-- The old-representative boundary and label relation are actually encoded;
    only new nodes are copied, and the full old transitive bound is fixed. -/
theorem mixed_tagged_graph_solution_exists (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) {a e S h D L labels : U}
    (hSD : Subset s S D) (hRange : RangeCode s a labels L) :
    ∃ f, MixedTaggedDecorationCode s a e S h labels f := by
  obtain ⟨B, hB⟩ := binary_union_exists base.pairing base.union D L
  obtain ⟨t, ht, hBt⟩ := transitive_cover_exists base B
  obtain ⟨u, hu⟩ := binary_union_exists base.pairing base.union a B
  obtain ⟨r, _, hr⟩ := normalized_relation_comprehension base mixedBoundaryFormula
    (cons a (cons S (cons h (cons e (cons labels Fin.elim0))))) u
  have hr' : ∀ x w, CodedRelation s r x w ↔ s x a ∧
      ((s w S ∧ ∃ d, CodedRelation s h w d ∧ CodedRelation s e x d) ∨ CodedRelation s labels x w) := by
    intro x w
    have hv := hr x w
    rw [eval_mixedBoundaryFormula] at hv
    refine hv.trans ⟨fun v => v.2.2, ?_⟩
    intro v
    refine ⟨(hu x).mpr (Or.inl v.1), (hu w).mpr (Or.inr ?_), v⟩
    rcases v.2 with hw | hl
    · exact (hB w).mpr (Or.inl (hSD w hw.1))
    · exact (hB w).mpr (Or.inr ((hRange w).mpr ⟨x, v.1, hl⟩))
  have hrt : ∀ x w, CodedRelation s r x w → s x a ∧ s w t := by
    intro x w hxw
    obtain ⟨hx, hw⟩ := (hr' x w).mp hxw
    refine ⟨hx, hBt w ((hB w).mpr ?_)⟩
    rcases hw with hw | hl
    · exact Or.inl (hSD w hw.1)
    · exact Or.inr ((hRange w).mpr ⟨x, hx, hl⟩)
  obtain ⟨en, henG, hen⟩ := normalized_relation_comprehension base (relatedFormula 2 1 0 : Formula 3)
    (cons e Fin.elim0) a
  have hen' : ∀ x y, CodedRelation s en x y ↔ s x a ∧ s y a ∧ CodedRelation s e x y := by
    intro x y
    have hv := hen x y
    simp only [eval_relatedFormula] at hv
    exact hv
  obtain ⟨f, hf⟩ := boundary_graph_solution_exists base hF henG ht hrt
  refine ⟨f, hf.1, ?_⟩
  intro x hx v hxv w
  refine (hf.2 x hx v hxv w).trans ⟨?_, ?_⟩
  · rintro (⟨y, hy, hxy, hyw⟩ | hboundary)
    · exact Or.inl ⟨y, hy, ((hen' x y).mp hxy).2.2, hyw⟩
    · exact Or.inr ((hr' x w).mp hboundary).2
  · rintro (⟨y, hy, hxy, hyw⟩ | hboundary)
    · exact Or.inl ⟨y, hy, (hen' x y).mpr ⟨hx, hy, hxy⟩, hyw⟩
    · exact Or.inr ((hr' x w).mpr ⟨hx, hboundary⟩)

/-- Labels separated from an old transitive bound force every new value outside
    that bound; after pruning, exactly the new and old successor edges remain. -/
theorem mixed_tagged_solution_pruning {a e S h labels f b D : U}
    (hb : SelfSingleton s b) (hD : TransitiveCode s D) (hSD : Subset s S D)
    (hSgood : ∀ w, s w S → ¬s b w)
    (hLabels : FunctionCode s a labels) (hLI : InjectiveCode s labels)
    (hbad : ∀ x l, CodedRelation s labels x l → s b l ∧ l ≠ b ∧ ¬s l D)
    (hf : MixedTaggedDecorationCode s a e S h labels f) :
    InjectiveCode s f ∧ (∀ x v, CodedRelation s f x v → ¬s b v ∧ ¬s v D) ∧
      ∀ x v, s x a → CodedRelation s f x v → ∀ w,
        PrunedMember s b v w ↔
          (∃ y, s y a ∧ CodedRelation s e x y ∧ CodedRelation s f y w) ∨
          (s w S ∧ ∃ d, CodedRelation s h w d ∧ CodedRelation s e x d) := by
  have hvb : ∀ x v, CodedRelation s f x v → v ≠ b := by
    intro x v hxv heq
    have hx := coded_function_domain hf.1 hxv
    obtain ⟨l, hxl, _⟩ := hLabels.2 x hx
    have hlv := (hf.2 x hx v hxv l).mpr (Or.inr (Or.inr hxl))
    exact (hbad x l hxl).2.1 ((hb l).mp (heq ▸ hlv))
  have hgood : ∀ x v, CodedRelation s f x v → ¬s b v := by
    intro x v hxv hbv
    rcases (hf.2 x (coded_function_domain hf.1 hxv) v hxv b).mp hbv with
      ⟨y, _, _, hyb⟩ | ⟨hbS, _⟩ | hxb
    · exact hvb y b hyb rfl
    · exact hSgood b hbS ((hb b).mpr rfl)
    · exact (hbad x b hxb).2.1 rfl
  have hout : ∀ x v, CodedRelation s f x v → ¬s v D := by
    intro x v hxv hvD
    have hx := coded_function_domain hf.1 hxv
    obtain ⟨l, hxl, _⟩ := hLabels.2 x hx
    exact (hbad x l hxl).2.2 (hD v hvD l ((hf.2 x hx v hxv l).mpr (Or.inr (Or.inr hxl))))
  refine ⟨?_, fun x v hxv => ⟨hgood x v hxv, hout x v hxv⟩, ?_⟩
  · intro x y v hxv hyv
    have hx := coded_function_domain hf.1 hxv
    obtain ⟨l, hxl, _⟩ := hLabels.2 x hx
    have hlv := (hf.2 x hx v hxv l).mpr (Or.inr (Or.inr hxl))
    rcases (hf.2 y (coded_function_domain hf.1 hyv) v hyv l).mp hlv with
      ⟨z, _, _, hzl⟩ | ⟨hlS, _⟩ | hyl
    · exact False.elim (hgood z l hzl (hbad x l hxl).1)
    · exact False.elim ((hbad x l hxl).2.2 (hSD l hlS))
    · exact hLI x y l hxl hyl
  · intro x v hx hxv w
    constructor
    · intro hpr
      rcases (hf.2 x hx v hxv w).mp hpr.2.2 with hn | ho | hl
      · exact Or.inl hn
      · exact Or.inr ho
      · exact False.elim (hpr.2.1 (hbad x w hl).1)
    · intro hw
      refine ⟨hgood x v hxv, ?_, (hf.2 x hx v hxv w).mpr ?_⟩
      · rcases hw with ⟨y, _, _, hyw⟩ | ⟨hwS, _⟩
        · exact hgood y w hyw
        · exact hSgood w hwS
      · rcases hw with hn | ho
        · exact Or.inl hn
        · exact Or.inr (Or.inl ho)

/-- All labels, boundary codes, new-edge restrictions and the new solution are
    constructed from the supplied actual old cover and classification relation. -/
theorem pruned_joint_graph_solution (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) {b a e S h D : U}
    (hb : SelfSingleton s b) (hD : TransitiveCode s D) (hSD : Subset s S D)
    (hSgood : ∀ w, s w S → ¬s b w) :
    ∃ f V, FunctionCode s a f ∧ InjectiveCode s f ∧ RangeCode s a f V ∧
      (∀ v, s v V → ¬s b v ∧ ¬s v D) ∧
      ∀ x v, s x a → CodedRelation s f x v → ∀ w,
        PrunedMember s b v w ↔
          (∃ y, s y a ∧ CodedRelation s e x y ∧ CodedRelation s f y w) ∨
          (s w S ∧ ∃ d, CodedRelation s h w d ∧ CodedRelation s e x d) := by
  obtain ⟨L, labels, hLF, hLI, hLR, hbad⟩ := excluded_label_family base hb a D
  obtain ⟨f, hf⟩ := mixed_tagged_graph_solution_exists base hF hSD hLR (e := e) (S := S) (h := h)
  have hbad' : ∀ x l, CodedRelation s labels x l → s b l ∧ l ≠ b ∧ ¬s l D := by
    intro x l hxl
    exact hbad l ((hLR l).mpr ⟨x, coded_function_domain hLF hxl, hxl⟩)
  obtain ⟨hfi, hgood, hrow⟩ := mixed_tagged_solution_pruning hb hD hSD hSgood hLF hLI hbad' hf
  obtain ⟨V, hV⟩ := coded_image_set_exists base f a
  refine ⟨f, V, hf.1, hfi, hV, ?_, hrow⟩
  intro v hv
  obtain ⟨x, _, hxv⟩ := (hV v).mp hv
  exact hgood x v hxv

/-- Old representatives and new solution values form an actual closed retained
    source set. Distinct representatives in the old part are still allowed. -/
theorem pruned_joint_closed_realization (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) {b a e S h D : U}
    (hb : SelfSingleton s b) (hD : TransitiveCode s D) (hSD : Subset s S D)
    (hSgood : ∀ w, s w S → ¬s b w)
    (hSclosed : ∀ x, s x S → ∀ y, PrunedMember s b x y → s y S) :
    ∃ f V C, FunctionCode s a f ∧ InjectiveCode s f ∧ RangeCode s a f V ∧
      (∀ v, s v V → ¬s v D) ∧ (∀ v, s v C ↔ s v S ∨ s v V) ∧
      (∀ v, s v C → ¬s b v) ∧
      (∀ v, s v C → ∀ w, PrunedMember s b v w → s w C) ∧
      ∀ x v, s x a → CodedRelation s f x v → ∀ w,
        PrunedMember s b v w ↔
          (∃ y, s y a ∧ CodedRelation s e x y ∧ CodedRelation s f y w) ∨
          (s w S ∧ ∃ d, CodedRelation s h w d ∧ CodedRelation s e x d) := by
  obtain ⟨f, V, hf, hi, hV, hgood, hrows⟩ := pruned_joint_graph_solution base hF hb hD hSD hSgood (a := a) (e := e) (h := h)
  obtain ⟨C, hC⟩ := binary_union_exists base.pairing base.union S V
  refine ⟨f, V, C, hf, hi, hV, fun v hv => (hgood v hv).2, hC, ?_, ?_, hrows⟩
  · intro v hv
    rcases (hC v).mp hv with hvS | hvV
    · exact hSgood v hvS
    · exact (hgood v hvV).1
  · intro v hv w hvw
    apply (hC w).mpr
    rcases (hC v).mp hv with hvS | hvV
    · exact Or.inl (hSclosed v hvS w hvw)
    · obtain ⟨x, hx, hxv⟩ := (hV v).mp hvV
      rcases (hrows x v hx hxv w).mp hvw with ⟨y, hy, _, hyw⟩ | ⟨hwS, _⟩
      · exact Or.inr ((hV w).mpr ⟨y, hy, hyw⟩)
      · exact Or.inl hwS

#print axioms pruned_joint_graph_solution
#print axioms pruned_joint_closed_realization
end FullBridge
