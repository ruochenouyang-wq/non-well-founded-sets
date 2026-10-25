import BehaviorChoice
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def BehaviorHomogeneous (s : U → U → Prop) (c : U) : Prop :=
  ∀ x y, s x c → s y c → InternalBehavior s x y

/-- Ordinary choice restricted to nonempty sets contained in single behavior fibers. -/
def FiberChoiceCode (s : U → U → Prop) : Prop :=
  ∀ a, (∀ c, s c a → (∃ x, s x c) ∧ BehaviorHomogeneous s c) →
    ∃ f, ChoiceFunctionCode s a f

def behaviorHomogeneousFormula {n} (c : Fin n) : Formula n :=
  .all (.all (.impl (.member 1 c.succ.succ)
    (.impl (.member 0 c.succ.succ) (internalBehaviorFormula 1 0))))

theorem eval_behaviorHomogeneousFormula (s : U → U → Prop) {n}
    (c : Fin n) (v : Fin n → U) :
    Eval s (behaviorHomogeneousFormula c) v ↔ BehaviorHomogeneous s (v c) := by
  simp only [behaviorHomogeneousFormula, Eval, eval_internalBehaviorFormula,
    BehaviorHomogeneous, cons_zero, cons_succ]
  rfl

def fiberChoiceSentence : Formula 0 :=
  .all (.impl (.all (.impl (.member 0 1)
    (.conj (.ex (.member 0 1)) (behaviorHomogeneousFormula 0))))
    (.ex (choiceFunctionFormula 1 0)))

theorem eval_fiberChoiceSentence (s : U → U → Prop) :
    Eval s fiberChoiceSentence Fin.elim0 ↔ FiberChoiceCode s := by
  simp only [fiberChoiceSentence, Eval, eval_behaviorHomogeneousFormula,
    eval_choiceFunctionFormula, FiberChoiceCode]
  rfl

def RelationRow (s : U → U → Prop) (r x c : U) : Prop :=
  ∀ y, s y c ↔ CodedRelation s r x y

def relationRowFormula {n} (r x c : Fin n) : Formula n :=
  .all ((Formula.member 0 c.succ).iffF (relatedFormula r.succ x.succ 0))

theorem eval_relationRowFormula (s : U → U → Prop) {n}
    (r x c : Fin n) (v : Fin n → U) :
    Eval s (relationRowFormula r x c) v ↔ RelationRow s (v r) (v x) (v c) := by
  simp only [relationRowFormula, Eval, eval_iffF, eval_relatedFormula,
    RelationRow, cons_zero, cons_succ]

theorem relation_row_exists (base : BaseCollection s) (r x : U) :
    ∃ c, RelationRow s r x c := by
  obtain ⟨d, hd⟩ := codedRelation_component_bound base.union r
  obtain ⟨c, hc⟩ := base.separation 2 (relatedFormula (n := 3) 2 1 0)
    (cons x (cons r Fin.elim0)) d
  refine ⟨c, ?_⟩
  intro y
  have h := hc y
  rw [eval_relatedFormula] at h
  change s y c ↔ s y d ∧ CodedRelation s r x y at h
  exact h.trans ⟨fun hy => hy.2, fun hy => ⟨(hd x y hy).2, hy⟩⟩

theorem relation_row_unique (base : BaseCollection s) {r x c d : U}
    (hc : RelationRow s r x c) (hd : RelationRow s r x d) : c = d :=
  base.extensional c d (fun y => (hc y).trans (hd y).symm)

theorem relation_row_family (base : BaseCollection s) (a r : U) :
    ∃ b, ∀ c, s c b ↔ ∃ x, s x a ∧ RelationRow s r x c := by
  obtain ⟨d, hd⟩ := codedRelation_component_bound base.union r
  obtain ⟨P, hP⟩ := base.powerset d
  obtain ⟨b, hb⟩ := base.separation 2
    (Formula.ex (.conj (.member 0 2) (relationRowFormula (n := 4) 3 0 1)))
    (cons a (cons r Fin.elim0)) P
  refine ⟨b, ?_⟩
  intro c
  have h := hb c
  simp only [Eval, eval_relationRowFormula] at h
  change s c b ↔ s c P ∧ ∃ x, s x a ∧ RelationRow s r x c at h
  constructor
  · exact fun hc => (h.mp hc).2
  · rintro ⟨x, hx, hrow⟩
    exact h.mpr ⟨(hP c).mpr (fun y hy => (hd x y ((hrow y).mp hy)).2), x, hx, hrow⟩

def resolvedChoiceFormula : Formula 5 :=
  .conj (.member 1 2) (.ex (.conj (relationRowFormula 4 2 0) (relatedFormula 5 0 1)))

theorem eval_resolvedChoiceFormula (s : U → U → Prop) (y x a r k : U) :
    Eval s resolvedChoiceFormula (cons y (cons x (cons a (cons r (cons k Fin.elim0))))) ↔
      s x a ∧ ∃ c, RelationRow s r x c ∧ CodedRelation s k c y := by
  simp only [resolvedChoiceFormula, Eval, eval_relationRowFormula, eval_relatedFormula]
  rfl

theorem fiber_choice_resolves_behavior_relation (base : BaseCollection s)
    (hFC : FiberChoiceCode s) {a r : U} (hr : BehaviorChoiceRelation s a r) :
    ∃ f, ChoiceFunctionCode s a f ∧
      ∀ x y, CodedRelation s f x y → CodedRelation s r x y := by
  obtain ⟨b, hb⟩ := relation_row_family base a r
  have hbh : ∀ c, s c b → (∃ y, s y c) ∧ BehaviorHomogeneous s c := by
    intro c hc
    obtain ⟨x, hx, hrow⟩ := (hb c).mp hc
    constructor
    · obtain ⟨y, hxy⟩ := hr.2.1 x hx
      exact ⟨y, (hrow y).mpr hxy⟩
    · intro y z hy hz
      exact hr.2.2.2 x x y z (internalBehavior_refl base.empty x)
        ((hrow y).mp hy) ((hrow z).mp hz)
  obtain ⟨k, hk⟩ := hFC b hbh
  obtain ⟨u, hu⟩ := base.union a
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union a u
  obtain ⟨f, hf⟩ := relation_comprehension_members base resolvedChoiceFormula
    (cons a (cons r (cons k Fin.elim0))) d
  have selected : ∀ x y, s x a →
      (∃ c, RelationRow s r x c ∧ CodedRelation s k c y) → CodedRelation s r x y := by
    rintro x y hx ⟨c, hc, hkcy⟩
    exact (hc y).mp (hk.2 c ((hb c).mpr ⟨x, hx, hc⟩) y hkcy)
  have hn : ∀ p, s p f → ∃ x y, s x a ∧ IsOrderedPair s p x y := by
    intro p hp
    obtain ⟨x, y, _, _, hpxy, hev⟩ := (hf p).mp hp
    exact ⟨x, y, ((eval_resolvedChoiceFormula s y x a r k).mp hev).1, hpxy⟩
  have hi : ∀ x y, CodedRelation s f x y ↔ s x a ∧
      ∃ c, RelationRow s r x c ∧ CodedRelation s k c y := by
    intro x y
    constructor
    · rintro ⟨p, hp, hpxy⟩
      obtain ⟨x', y', _, _, hp', hev⟩ := (hf p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxy hp'
      exact (eval_resolvedChoiceFormula s y x a r k).mp hev
    · rintro ⟨hx, hw⟩
      have hyx := hr.2.2.1 x y (selected x y hx hw)
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x y
      exact ⟨p, (hf p).mpr ⟨x, y, (hd x).mpr (Or.inl hx),
        (hd y).mpr (Or.inr ((hu y).mpr ⟨x, hx, hyx⟩)), hp,
        (eval_resolvedChoiceFormula s y x a r k).mpr ⟨hx, hw⟩⟩, hp⟩
  have hsub : ∀ x y, CodedRelation s f x y → CodedRelation s r x y := by
    intro x y hxy
    exact selected x y ((hi x y).mp hxy).1 ((hi x y).mp hxy).2
  refine ⟨f, ⟨⟨hn, ?_⟩, ?_⟩, hsub⟩
  · intro x hx
    obtain ⟨c, hc⟩ := relation_row_exists base r x
    have hcb := (hb c).mpr ⟨x, hx, hc⟩
    obtain ⟨y, hky, huniq⟩ := hk.1.2 c hcb
    refine ⟨y, (hi x y).mpr ⟨hx, c, hc, hky⟩, ?_⟩
    intro z hxz
    obtain ⟨_, c', hc', hkz⟩ := (hi x z).mp hxz
    have heq := relation_row_unique base hc' hc
    subst c'
    exact huniq z hkz
  · intro x _ y hxy
    exact hr.2.2.1 x y (hsub x y hxy)

theorem fiber_choice_lifts_target_function (base : BaseCollection s)
    (hFC : FiberChoiceCode s) (a : U) (F : InternalQuotient base)
    (hF : ChoiceFunctionCode (internalMember base) (internalCode base a) F) :
    ∃ f, ChoiceFunctionCode s a f ∧ internalCode base f = F := by
  obtain ⟨r, hr, hrF⟩ := behavior_choice_relation_pullback base a F hF
  obtain ⟨f, hf, hsub⟩ := fiber_choice_resolves_behavior_relation base hFC hr
  have hqf : ChoiceFunctionCode (internalMember base) (internalCode base a) (internalCode base f) := by
    apply choiceFunction_forward_compatible (internal_exact_members base) hf
    intro x x' y y' _ _ hxx hxy hx'y'
    exact (internal_code_eq base y y').mpr (hr.2.2.2 x x' y y'
      ((internal_code_eq base x x').mp hxx) (hsub x y hxy) (hsub x' y' hx'y'))
  have hqr := behavior_choice_relation_forward base hr
  have hfr : internalCode base f = internalCode base r := by
    apply function_code_extensional (internal_extensional base) hqf.1 hqr.1
    intro X Y Z hXY hXZ
    obtain ⟨x, y, hx, hxy, rfl, rfl⟩ :=
      (codedRelation_image (internal_exact_members base) hf.1.1 X Y).mp hXY
    obtain ⟨W, _, hu⟩ := hqr.1.2 _ ((internal_exact_members base a _).mpr ⟨x, hx, rfl⟩)
    exact (hu _ (codedRelation_forward (internal_exact_members base) (hsub x y hxy))).trans
      (hu _ hXZ).symm
  exact ⟨f, hf, hfr.trans hrF⟩

theorem source_choice_iff_behavior_and_fiber (base : BaseCollection s) :
    ChoiceCode s ↔ BehaviorChoiceCode s ∧ FiberChoiceCode s := by
  constructor
  · intro hAC
    exact ⟨source_choice_implies_behavior_choice base hAC,
      fun a ha => hAC a (fun c hc => (ha c hc).1)⟩
  · rintro ⟨hBC, hFC⟩ a ha
    obtain ⟨r, hr⟩ := hBC a ha
    obtain ⟨f, hf, _⟩ := fiber_choice_resolves_behavior_relation base hFC hr
    exact ⟨f, hf⟩

theorem source_choice_iff_target_and_fiber (base : BaseCollection s) :
    ChoiceCode s ↔ ChoiceCode (internalMember base) ∧ FiberChoiceCode s := by
  rw [quotient_choice_iff_behavior_choice]
  exact source_choice_iff_behavior_and_fiber base

theorem choice_sentence_decomposition (base : BaseCollection s) :
    Eval s choiceSentence Fin.elim0 ↔
      Eval s (Formula.conj behaviorChoiceSentence fiberChoiceSentence) Fin.elim0 := by
  simp only [Eval, eval_choiceSentence, eval_behaviorChoiceSentence, eval_fiberChoiceSentence]
  exact source_choice_iff_behavior_and_fiber base

#print axioms fiber_choice_resolves_behavior_relation
#print axioms source_choice_iff_target_and_fiber
#print axioms choice_sentence_decomposition
end FullBridge
