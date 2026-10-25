import PrunedCarrierComparison
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Ordinary object Choice resolves any actual total coded relation on a set;
    values are not required to be members of their input objects. -/
theorem choice_resolves_total_relation (base : BaseCollection s) (hAC : ChoiceCode s)
    {a r : U} (htotal : ∀ x, s x a → ∃ y, CodedRelation s r x y) :
    ∃ f, FunctionCode s a f ∧ ∀ x y, CodedRelation s f x y → CodedRelation s r x y := by
  obtain ⟨B, hB⟩ := relation_row_family base a r
  have hBne : ∀ c, s c B → ∃ y, s y c := by
    intro c hc
    obtain ⟨x, hx, hrow⟩ := (hB c).mp hc
    obtain ⟨y, hxy⟩ := htotal x hx
    exact ⟨y, (hrow y).mpr hxy⟩
  obtain ⟨k, hk⟩ := hAC B hBne
  obtain ⟨bound, hbound⟩ := codedRelation_component_bound base.union r
  obtain ⟨u, hu⟩ := binary_union_exists base.pairing base.union a bound
  obtain ⟨f, hmem⟩ := relation_comprehension_members base resolvedChoiceFormula
    (cons a (cons r (cons k Fin.elim0))) u
  have hselected : ∀ x y, s x a →
      (∃ c, RelationRow s r x c ∧ CodedRelation s k c y) → CodedRelation s r x y := by
    rintro x y hx ⟨c, hc, hcy⟩
    exact (hc y).mp (hk.2 c ((hB c).mpr ⟨x, hx, hc⟩) y hcy)
  have hf : ∀ x y, CodedRelation s f x y ↔ s x a ∧
      ∃ c, RelationRow s r x c ∧ CodedRelation s k c y := by
    intro x y
    constructor
    · rintro ⟨p, hp, hpxy⟩
      obtain ⟨x', y', _, _, hp', hev⟩ := (hmem p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxy hp'
      exact (eval_resolvedChoiceFormula s y x a r k).mp hev
    · rintro ⟨hx, hc⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x y
      exact ⟨p, (hmem p).mpr ⟨x, y, (hu x).mpr (Or.inl hx),
        (hu y).mpr (Or.inr (hbound x y (hselected x y hx hc)).2), hp,
        (eval_resolvedChoiceFormula s y x a r k).mpr ⟨hx, hc⟩⟩, hp⟩
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨x, y, _, _, hpxy, hev⟩ := (hmem p).mp hp
    exact ⟨x, y, ((eval_resolvedChoiceFormula s y x a r k).mp hev).1, hpxy⟩
  · intro x hx
    obtain ⟨c, hc⟩ := relation_row_exists base r x
    obtain ⟨y, hcy, huq⟩ := hk.1.2 c ((hB c).mpr ⟨x, hx, hc⟩)
    refine ⟨y, (hf x y).mpr ⟨hx, c, hc, hcy⟩, ?_⟩
    intro z hxz
    obtain ⟨_, d, hd, hdz⟩ := (hf x z).mp hxz
    have hdc := relation_row_unique base hd hc
    subst d
    exact huq z hdz
  · intro x y hxy
    obtain ⟨hx, hc⟩ := (hf x y).mp hxy
    exact hselected x y hx hc

def prunedChoiceCandidatesFormula : Formula 4 :=
  .conj (.member 1 2) (.ex (.conj (.member 0 2)
    (.conj (.impl (.member 4 0) .bottom)
      (.conj (.impl (.member 4 1) .bottom) (.member 1 0)))))

theorem eval_prunedChoiceCandidatesFormula (a b c y : U) :
    Eval s prunedChoiceCandidatesFormula (cons y (cons c (cons a (cons b Fin.elim0)))) ↔
      s c a ∧ ∃ x, s x c ∧ PrunedMember s b x y := by
  simp only [prunedChoiceCandidatesFormula, Eval, PrunedMember]
  rfl

/-- For each actual node class, gather retained members of all its representatives.
    A selector on these rows is automatically coordinated by target identity. -/
theorem pruned_choice_candidates (base : BaseCollection s) {b : U} (hbb : s b b)
    {A : PrunedQuotient base b} (P : PrunedNodePresentation base b A)
    (hA : ∀ X, prunedMember base b X A → ∃ Y, prunedMember base b Y X) :
    ∃ r, (∀ c y, CodedRelation s r c y ↔ s c P.nodes ∧ ∃ x, s x c ∧ PrunedMember s b x y) ∧
      ∀ c, s c P.nodes → ∃ y, CodedRelation s r c y := by
  obtain ⟨v, hv⟩ := base.union P.representatives
  obtain ⟨u, hu⟩ := binary_union_exists base.pairing base.union P.nodes v
  obtain ⟨r, _, hr⟩ := normalized_relation_comprehension base prunedChoiceCandidatesFormula
    (cons P.nodes (cons b Fin.elim0)) u
  have hr' : ∀ c y, CodedRelation s r c y ↔ s c P.nodes ∧ ∃ x, s x c ∧ PrunedMember s b x y := by
    intro c y
    have h := hr c y
    rw [eval_prunedChoiceCandidatesFormula] at h
    refine h.trans ⟨fun h => h.2.2, ?_⟩
    intro hxy
    obtain ⟨hc, x, hxc, hpr⟩ := hxy
    obtain ⟨z, _, hzc⟩ := (P.nodes_iff c).mp hc
    have hx := ((hzc x).mp hxc).1
    exact ⟨(hu c).mpr (Or.inl hc), (hu y).mpr (Or.inr ((hv y).mpr ⟨x, hx, hpr.2.2⟩)), hc, x, hxc, hpr⟩
  refine ⟨r, hr', ?_⟩
  intro c hc
  obtain ⟨x, hx, hxc⟩ := (P.nodes_iff c).mp hc
  have hxA : prunedMember base b (prunedCode base b x) A := by
    have h := ((pruned_good_row base hbb P.clean).2 _).mpr ⟨x, hx, rfl⟩
    simpa only [P.image] using h
  obtain ⟨Y, hY⟩ := hA _ hxA
  obtain ⟨y, hxy, _⟩ := (least_global_exact_members base prunedMemberFormula
    (cons b Fin.elim0) (pruned_edges_are_members b) x Y).mp hY
  have hxx : s x c := (hxc x).mpr ⟨hx, (P.relation_iff x x).mpr ⟨hx, hx, rfl⟩⟩
  exact ⟨y, (hr' c y).mpr ⟨hc, x, hxx, hxy⟩⟩

/-- Source object Choice passes to the actual pruned least quotient. Only B and
    b member b are needed; no anti-foundation or fixed graph solver is used. -/
theorem pruned_quotient_choice (base : BaseCollection s) (hAC : ChoiceCode s)
    {b : U} (hbb : s b b) : ChoiceCode (prunedMember base b) := by
  intro A hA
  obtain ⟨P⟩ := pruned_node_presentation_exists base hbb A
  obtain ⟨r, hr, htotal⟩ := pruned_choice_candidates base hbb P hA
  obtain ⟨f, hf, hsub⟩ := choice_resolves_total_relation base hAC htotal
  obtain ⟨g, hg, hgp⟩ := pruned_class_pullback_function base P hf
  have hgood : ∀ x y, CodedRelation s g x y → ¬s b y := by
    intro x y hxy
    obtain ⟨_, c, _, hcy⟩ := (hgp x y).mp hxy
    obtain ⟨_, z, _, hzy⟩ := (hr c y).mp (hsub c y hcy)
    exact hzy.2.1
  have hcoh : ∀ x x' y y', CodedRelation s g x y → CodedRelation s g x' y' →
      prunedCode base b x = prunedCode base b x' → prunedCode base b y = prunedCode base b y' := by
    intro x x' y y' hxy hx'y' heq
    obtain ⟨hx, c, hxc, hcy⟩ := (hgp x y).mp hxy
    obtain ⟨hx', d, hx'd, hdy'⟩ := (hgp x' y').mp hx'y'
    have hcd := (pruned_node_class_eq base P hx hx' hxc hx'd).mpr heq
    subst d
    exact congrArg (prunedCode base b) (coded_function_value_unique hf hcy hdy')
  have hq0 := pruned_function_forward base hbb hg P.clean hgood hcoh
  have hq : FunctionCode (prunedMember base b) A (prunedCode base b g) := by
    simpa only [P.image] using hq0
  refine ⟨prunedCode base b g, hq, ?_⟩
  intro X _ Y hXY
  obtain ⟨x, y, hxy, hqx, hqy⟩ :=
    (pruned_coded_relation_image base hbb (pruned_function_retained hg P.clean hgood) X Y).mp hXY
  obtain ⟨_, c, hxc, hcy⟩ := (hgp x y).mp hxy
  obtain ⟨_, z, hzc, hzy⟩ := (hr c y).mp (hsub c y hcy)
  have hqzx : prunedCode base b z = prunedCode base b x :=
    ((P.relation_iff x z).mp ((hxc z).mp hzc).2).2.2.symm
  have hYz : prunedMember base b Y (prunedCode base b z) :=
    (least_global_exact_members base prunedMemberFormula (cons b Fin.elim0)
      (pruned_edges_are_members b) z Y).mpr ⟨y, hzy, hqy⟩
  exact (hqzx.trans hqx) ▸ hYz

#print axioms pruned_quotient_choice
end FullBridge
