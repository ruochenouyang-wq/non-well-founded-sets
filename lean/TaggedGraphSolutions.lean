import ExcludedLabelFamilies
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem coded_function_value_unique {a f x y z : U} (hf : FunctionCode s a f)
    (hxy : CodedRelation s f x y) (hxz : CodedRelation s f x z) : y = z := by
  obtain ⟨v, _, hv⟩ := hf.2 x (coded_function_domain hf hxy)
  exact (hv y hxy).trans (hv z hxz).symm

def TaggedDecorationCode (s : U → U → Prop) (a e labels f : U) : Prop :=
  FunctionCode s a f ∧ ∀ x, s x a → ∀ v, CodedRelation s f x v →
    ∀ w, s w v ↔ (∃ y, s y a ∧ CodedRelation s e x y ∧ CodedRelation s f y w) ∨
      CodedRelation s labels x w

def CopiedTaggedEdge (s : U → U → Prop) (t e k labels x y : U) : Prop :=
  (s x t ∧ s y x) ∨ ∃ z, CodedRelation s k z x ∧
    ((∃ w, CodedRelation s e z w ∧ CodedRelation s k w y) ∨ CodedRelation s labels z y)

def copiedTaggedEdgeFormula : Formula 6 :=
  (Formula.conj (.member 1 2) (.member 0 1)).disj
    (.ex (.conj (relatedFormula 5 0 2)
      ((Formula.ex (.conj (relatedFormula 5 1 0) (relatedFormula 6 0 2))).disj
        (relatedFormula 6 0 1))))

theorem eval_copiedTaggedEdgeFormula (t e k labels x y : U) :
    Eval s copiedTaggedEdgeFormula (cons y (cons x (cons t (cons e (cons k (cons labels Fin.elim0)))))) ↔
      CopiedTaggedEdge s t e k labels x y := by
  simp only [copiedTaggedEdgeFormula, eval_disj, Eval, eval_relatedFormula, CopiedTaggedEdge]
  rfl

/-- Arbitrary internally coded graph equations with one prescribed label per
    node are solved by an actual source function, using fixed-part solvability. -/
theorem tagged_graph_solution_exists (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) {a e L labels : U}
    (hG : GraphCode s a e) (hLabels : FunctionCode s a labels)
    (hRange : RangeCode s a labels L) : ∃ f, TaggedDecorationCode s a e labels f := by
  obtain ⟨t, ht, hLt⟩ := transitive_cover_exists base L
  obtain ⟨c, k, hkF, hkI, hkR, hkFresh⟩ := fresh_parameter_copy base a t
  have hkC : ∀ x z, CodedRelation s k x z → s z c :=
    fun x z h => (hkR z).mpr ⟨x, coded_function_domain hkF h, h⟩
  have hlT : ∀ x l, CodedRelation s labels x l → s l t :=
    fun x l h => hLt l ((hRange l).mpr ⟨x, coded_function_domain hLabels h, h⟩)
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

/-- Excluded labels force the source solution to be injective and retained;
    pruning removes exactly the label edges. -/
theorem tagged_solution_pruning {a e labels f b : U}
    (hb : SelfSingleton s b) (hLabels : FunctionCode s a labels) (hLI : InjectiveCode s labels)
    (hbad : ∀ x l, CodedRelation s labels x l → s b l ∧ l ≠ b)
    (hf : TaggedDecorationCode s a e labels f) :
    InjectiveCode s f ∧ (∀ x v, CodedRelation s f x v → ¬s b v) ∧
      ∀ x v, s x a → CodedRelation s f x v → ∀ w,
        PrunedMember s b v w ↔ ∃ y, s y a ∧ CodedRelation s e x y ∧ CodedRelation s f y w := by
  have hvb : ∀ x v, CodedRelation s f x v → v ≠ b := by
    intro x v hxv heq
    have hx := coded_function_domain hf.1 hxv
    obtain ⟨l, hxl, _⟩ := hLabels.2 x hx
    have hlv := (hf.2 x hx v hxv l).mpr (Or.inr hxl)
    exact (hbad x l hxl).2 ((hb l).mp (heq ▸ hlv))
  have hgood : ∀ x v, CodedRelation s f x v → ¬s b v := by
    intro x v hxv hbv
    rcases (hf.2 x (coded_function_domain hf.1 hxv) v hxv b).mp hbv with ⟨y, _, _, hyb⟩ | hxb
    · exact hvb y b hyb rfl
    · exact (hbad x b hxb).2 rfl
  refine ⟨?_, hgood, ?_⟩
  · intro x y v hxv hyv
    have hx := coded_function_domain hf.1 hxv
    obtain ⟨l, hxl, _⟩ := hLabels.2 x hx
    have hlv := (hf.2 x hx v hxv l).mpr (Or.inr hxl)
    rcases (hf.2 y (coded_function_domain hf.1 hyv) v hyv l).mp hlv with ⟨z, _, _, hzl⟩ | hyl
    · exact False.elim (hgood z l hzl (hbad x l hxl).1)
    · exact hLI x y l hxl hyl
  · intro x v hx hxv w
    constructor
    · intro h
      rcases (hf.2 x hx v hxv w).mp h.2.2 with hrow | hlabel
      · exact hrow
      · exact False.elim (h.2.1 (hbad x w hlabel).1)
    · rintro ⟨y, hy, hxy, hyw⟩
      exact ⟨hgood x v hxv, hgood y w hyw, (hf.2 x hx v hxv w).mpr (Or.inl ⟨y, hy, hxy, hyw⟩)⟩

/-- The label and function interfaces are discharged for every source-coded
    graph; its actual image is a closed retained subgraph of the pruned universe. -/
theorem pruned_source_graph_realization (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) {b a e : U} (hb : SelfSingleton s b)
    (hG : GraphCode s a e) :
    ∃ f T, FunctionCode s a f ∧ InjectiveCode s f ∧ RangeCode s a f T ∧
      (∀ v, s v T → ¬s b v) ∧
      ∀ x v, s x a → CodedRelation s f x v → ∀ w,
        PrunedMember s b v w ↔ ∃ y, s y a ∧ CodedRelation s e x y ∧ CodedRelation s f y w := by
  obtain ⟨L, labels, hLF, hLI, hLR, hbad⟩ := excluded_label_family base hb a a
  obtain ⟨f, hf⟩ := tagged_graph_solution_exists base hF hG hLF hLR
  have hbad' : ∀ x l, CodedRelation s labels x l → s b l ∧ l ≠ b := by
    intro x l hxl
    have h := hbad l ((hLR l).mpr ⟨x, coded_function_domain hLF hxl, hxl⟩)
    exact ⟨h.1, h.2.1⟩
  obtain ⟨hfi, hgood, hrows⟩ := tagged_solution_pruning hb hLF hLI hbad' hf
  obtain ⟨T, hT⟩ := coded_image_set_exists base f a
  refine ⟨f, T, hf.1, hfi, hT, ?_, hrows⟩
  intro v hv
  obtain ⟨x, _, hxv⟩ := (hT v).mp hv
  exact hgood x v hxv

/-- Source-coded extensional graphs embed through the actual least quotient.
    This does not yet lift arbitrary target-coded graphs or fix a prescribed
    target transitive parameter, so it is not the target BAFA axiom. -/
theorem pruned_extensional_source_graph_embedding (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) {b a e : U} (hb : SelfSingleton s b)
    (hG : GraphCode s a e) (hext : GraphExtensionalCode s a e) :
    ∃ f T, FunctionCode s a f ∧ InjectiveCode s f ∧ RangeCode s a f T ∧
      (∀ v, s v T → ¬s b v) ∧ TransitiveCode (prunedMember base b) (prunedCode base b T) ∧
      ∀ x y v w, CodedRelation s f x v → CodedRelation s f y w →
        (prunedCode base b v = prunedCode base b w ↔ x = y) ∧
        (prunedMember base b (prunedCode base b w) (prunedCode base b v) ↔ CodedRelation s e x y) := by
  obtain ⟨f, T, hf, hfi, hT, hgood, hrows⟩ := pruned_source_graph_realization base hF hb hG
  have hin : ∀ x v, CodedRelation s f x v → s v T :=
    fun x v hxv => (hT v).mpr ⟨x, coded_function_domain hf hxv, hxv⟩
  have hclosed : ∀ v, s v T → ∀ w,
      FormulaEdges s prunedMemberFormula (cons b Fin.elim0) v w → s w T := by
    intro v hv w hvw
    obtain ⟨x, hx, hxv⟩ := (hT v).mp hv
    obtain ⟨y, hy, _, hyw⟩ := (hrows x v hx hxv w).mp hvw
    exact (hT w).mpr ⟨y, hy, hyw⟩
  have hedge : ∀ x y v w, CodedRelation s f x v → CodedRelation s f y w →
      (PrunedMember s b v w ↔ CodedRelation s e x y) := by
    intro x y v w hxv hyw
    refine (hrows x v (coded_function_domain hf hxv) hxv w).trans ⟨?_, ?_⟩
    · rintro ⟨z, _, hxz, hzw⟩
      have hzy := hfi z y w hzw hyw
      exact hzy ▸ hxz
    · intro hxy
      exact ⟨y, coded_function_domain hf hyw, hxy, hyw⟩
  have hTExt : ∀ v, s v T → ∀ w, s w T →
      (∀ z, s z T → (FormulaEdges s prunedMemberFormula (cons b Fin.elim0) v z ↔
        FormulaEdges s prunedMemberFormula (cons b Fin.elim0) w z)) → v = w := by
    intro v hv w hw he
    obtain ⟨x, hx, hxv⟩ := (hT v).mp hv
    obtain ⟨y, hy, hyw⟩ := (hT w).mp hw
    have hxy : x = y := by
      apply hext x hx y hy
      intro z hz
      obtain ⟨u, hzu, _⟩ := hf.2 z hz
      exact (hedge x z v u hxv hzu).symm.trans ((he u (hin z u hzu)).trans (hedge y z w u hyw hzu))
    subst y
    exact coded_function_value_unique hf hxv hyw
  refine ⟨f, T, hf, hfi, hT, hgood, ?_, ?_⟩
  · intro X hX Y hY
    obtain ⟨v, hv, rfl⟩ := ((pruned_good_row base ((hb b).mpr rfl) hgood).2 X).mp hX
    obtain ⟨w, hvw, rfl⟩ := (least_global_exact_members base prunedMemberFormula
      (cons b Fin.elim0) (pruned_edges_are_members b) v Y).mp hY
    exact ((pruned_good_row base ((hb b).mpr rfl) hgood).2 _).mpr ⟨w, hclosed v hv w hvw, rfl⟩
  · intro x y v w hxv hyw
    have hqc := least_global_injective_on_closed base prunedMemberFormula (cons b Fin.elim0)
      (pruned_edges_are_members b) T hclosed hTExt (hin x v hxv) (hin y w hyw)
    refine ⟨hqc.trans ⟨?_, ?_⟩, ?_⟩
    · intro hvw
      subst w
      exact hfi x y v hxv hyw
    · intro hxy
      subst y
      exact coded_function_value_unique hf hxv hyw
    · exact (least_global_reflects_closed_edges base prunedMemberFormula (cons b Fin.elim0)
        (pruned_edges_are_members b) T hclosed hTExt (hin x v hxv) (hin y w hyw)).trans
        (hedge x y v w hxv hyw)

#print axioms tagged_graph_solution_exists
#print axioms pruned_extensional_source_graph_embedding
end FullBridge
