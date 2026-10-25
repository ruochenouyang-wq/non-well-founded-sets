import CoherentRestrictions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A total internal relation selecting actual members, single-valued modulo internal behavior. -/
def BehaviorChoiceRelation (s : U → U → Prop) (a r : U) : Prop :=
  (∀ p, s p r → ∃ x y, s x a ∧ IsOrderedPair s p x y) ∧
  (∀ x, s x a → ∃ y, CodedRelation s r x y) ∧
  (∀ x y, CodedRelation s r x y → s y x) ∧
  ∀ x x' y y', InternalBehavior s x x' →
    CodedRelation s r x y → CodedRelation s r x' y' → InternalBehavior s y y'

def BehaviorChoiceCode (s : U → U → Prop) : Prop :=
  ∀ a, (∀ x, s x a → ∃ y, s y x) → ∃ r, BehaviorChoiceRelation s a r

def behaviorChoiceRelationFormula {n} (a r : Fin n) : Formula n :=
  .conj
    (.all (.impl (.member 0 r.succ) (.ex (.ex (.conj (.member 1 a.succ.succ.succ)
      (orderedPairFormula 2 1 0))))))
    (.conj
      (.all (.impl (.member 0 a.succ) (.ex (relatedFormula r.succ.succ 1 0))))
      (.conj
        (.all (.all (.impl (relatedFormula r.succ.succ 1 0) (.member 0 1))))
        (.all (.all (.all (.all (.impl (internalBehaviorFormula 3 2)
          (.impl (relatedFormula r.succ.succ.succ.succ 3 1)
            (.impl (relatedFormula r.succ.succ.succ.succ 2 0)
              (internalBehaviorFormula 1 0))))))))))

theorem eval_behaviorChoiceRelationFormula (s : U → U → Prop) {n}
    (a r : Fin n) (e : Fin n → U) :
    Eval s (behaviorChoiceRelationFormula a r) e ↔ BehaviorChoiceRelation s (e a) (e r) := by
  simp only [behaviorChoiceRelationFormula, Eval, eval_orderedPairFormula,
    eval_relatedFormula, eval_internalBehaviorFormula, BehaviorChoiceRelation, cons_zero, cons_succ]
  rfl

def behaviorChoiceSentence : Formula 0 :=
  .all (.impl (.all (.impl (.member 0 1) (.ex (.member 0 1))))
    (.ex (behaviorChoiceRelationFormula 1 0)))

theorem eval_behaviorChoiceSentence (s : U → U → Prop) :
    Eval s behaviorChoiceSentence Fin.elim0 ↔ BehaviorChoiceCode s := by
  simp only [behaviorChoiceSentence, Eval, eval_behaviorChoiceRelationFormula, BehaviorChoiceCode]
  rfl

theorem behavior_choice_relation_forward (base : BaseCollection s) {a r : U}
    (hr : BehaviorChoiceRelation s a r) :
    ChoiceFunctionCode (internalMember base) (internalCode base a) (internalCode base r) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro P hP
    obtain ⟨p, hp, rfl⟩ := (internal_exact_members base r P).mp hP
    obtain ⟨x, y, hx, hpxy⟩ := hr.1 p hp
    exact ⟨internalCode base x, internalCode base y,
      (internal_exact_members base a _).mpr ⟨x, hx, rfl⟩,
      orderedPair_forward (internal_exact_members base) hpxy⟩
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := (internal_exact_members base a X).mp hX
    obtain ⟨y, hxy⟩ := hr.2.1 x hx
    refine ⟨internalCode base y, codedRelation_forward (internal_exact_members base) hxy, ?_⟩
    intro Z hZ
    obtain ⟨x', z, _, hxz, hxx, rfl⟩ :=
      (codedRelation_image (internal_exact_members base) hr.1 (internalCode base x) Z).mp hZ
    exact (internal_code_eq base z y).mpr (hr.2.2.2 x' x z y
      ((internal_code_eq base x' x).mp hxx) hxz hxy)
  · intro X _ Y hXY
    obtain ⟨x, y, _, hxy, rfl, rfl⟩ :=
      (codedRelation_image (internal_exact_members base) hr.1 X Y).mp hXY
    exact (internal_exact_members base x _).mpr ⟨y, hr.2.2.1 x y hxy, rfl⟩

def choicePullbackFormula (eqF memF : Formula 2) : Formula 4 :=
  .conj (.member 1 2) (.conj (.member 0 1)
    (Formula.translate eqF memF (relatedFormula 3 1 0)))

theorem eval_choicePullbackFormula (base : BaseCollection s) (y x a f : U) :
    Eval s (choicePullbackFormula (internalInterpretation base).equalFormula
      (internalInterpretation base).memberFormula) (cons y (cons x (cons a (cons f Fin.elim0)))) ↔
    s x a ∧ s y x ∧ CodedRelation (internalMember base) (internalCode base f)
      (internalCode base x) (internalCode base y) := by
  have h := internal_formula_translation base (relatedFormula (n := 4) 3 1 0)
    (cons y (cons x (cons a (cons f Fin.elim0))))
  rw [eval_relatedFormula] at h
  change (s x a ∧ s y x ∧ Eval s (Formula.translate (internalInterpretation base).equalFormula
    (internalInterpretation base).memberFormula (relatedFormula 3 1 0))
    (cons y (cons x (cons a (cons f Fin.elim0))))) ↔ _
  exact and_congr_right (fun _ => and_congr_right (fun _ => h))

theorem behavior_choice_relation_pullback (base : BaseCollection s) (a : U)
    (F : InternalQuotient base)
    (hF : ChoiceFunctionCode (internalMember base) (internalCode base a) F) :
    ∃ r, BehaviorChoiceRelation s a r ∧ internalCode base r = F := by
  obtain ⟨f, rfl⟩ := internal_code_onto base F
  obtain ⟨u, hu⟩ := base.union a
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union a u
  obtain ⟨r, hr⟩ := relation_comprehension_members base
    (choicePullbackFormula (internalInterpretation base).equalFormula
      (internalInterpretation base).memberFormula) (cons a (cons f Fin.elim0)) d
  have hn : ∀ p, s p r → ∃ x y, s x a ∧ IsOrderedPair s p x y := by
    intro p hp
    obtain ⟨x, y, _, _, hpxy, hev⟩ := (hr p).mp hp
    exact ⟨x, y, ((eval_choicePullbackFormula base y x a f).mp hev).1, hpxy⟩
  have hi : ∀ x y, CodedRelation s r x y ↔ s x a ∧ s y x ∧
      CodedRelation (internalMember base) (internalCode base f)
        (internalCode base x) (internalCode base y) := by
    intro x y
    constructor
    · rintro ⟨p, hp, hpxy⟩
      obtain ⟨x', y', _, _, hp', hev⟩ := (hr p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxy hp'
      exact (eval_choicePullbackFormula base y x a f).mp hev
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x y
      exact ⟨p, (hr p).mpr ⟨x, y, (hd x).mpr (Or.inl hx),
        (hd y).mpr (Or.inr ((hu y).mpr ⟨x, hx, hy⟩)), hp,
        (eval_choicePullbackFormula base y x a f).mpr ⟨hx, hy, hxy⟩⟩, hp⟩
  have hb : BehaviorChoiceRelation s a r := by
    refine ⟨hn, ?_, ?_, ?_⟩
    · intro x hx
      have hqx := (internal_exact_members base a _).mpr ⟨x, hx, rfl⟩
      obtain ⟨Y, hXY, _⟩ := hF.1.2 _ hqx
      obtain ⟨y, hy, rfl⟩ := (internal_exact_members base x Y).mp (hF.2 _ hqx Y hXY)
      exact ⟨y, (hi x y).mpr ⟨hx, hy, hXY⟩⟩
    · intro x y hxy
      exact ((hi x y).mp hxy).2.1
    · intro x x' y y' hxx hxy hx'y'
      obtain ⟨hx, _, hXY⟩ := (hi x y).mp hxy
      have hX'Y' := ((hi x' y').mp hx'y').2.2
      have hqq := (internal_code_eq base x x').mpr hxx
      rw [← hqq] at hX'Y'
      obtain ⟨Z, _, huniq⟩ := hF.1.2 _ ((internal_exact_members base a _).mpr ⟨x, hx, rfl⟩)
      exact (internal_code_eq base y y').mp
        ((huniq _ hXY).trans (huniq _ hX'Y').symm)
  refine ⟨r, hb, ?_⟩
  apply function_code_extensional (internal_extensional base)
    (behavior_choice_relation_forward base hb).1 hF.1
  intro X Y Z hXY hXZ
  obtain ⟨x, y, hx, hxy, rfl, rfl⟩ :=
    (codedRelation_image (internal_exact_members base) hn X Y).mp hXY
  obtain ⟨W, _, huniq⟩ := hF.1.2 _ ((internal_exact_members base a _).mpr ⟨x, hx, rfl⟩)
  exact (huniq _ ((hi x y).mp hxy).2.2).trans (huniq _ hXZ).symm

theorem quotient_choice_iff_behavior_choice (base : BaseCollection s) :
    ChoiceCode (internalMember base) ↔ BehaviorChoiceCode s := by
  constructor
  · intro hAC a ha
    have hqa : ∀ X, internalMember base X (internalCode base a) → ∃ Y, internalMember base Y X := by
      intro X hX
      obtain ⟨x, hx, rfl⟩ := (internal_exact_members base a X).mp hX
      obtain ⟨y, hy⟩ := ha x hx
      exact ⟨internalCode base y, (internal_exact_members base x _).mpr ⟨y, hy, rfl⟩⟩
    obtain ⟨F, hF⟩ := hAC _ hqa
    obtain ⟨r, hr, _⟩ := behavior_choice_relation_pullback base a F hF
    exact ⟨r, hr⟩
  · intro hBC A hA
    obtain ⟨a, rfl⟩ := internal_code_onto base A
    have ha : ∀ x, s x a → ∃ y, s y x := by
      intro x hx
      obtain ⟨Y, hY⟩ := hA _ ((internal_exact_members base a _).mpr ⟨x, hx, rfl⟩)
      obtain ⟨y, hy, _⟩ := (internal_exact_members base x Y).mp hY
      exact ⟨y, hy⟩
    obtain ⟨r, hr⟩ := hBC a ha
    exact ⟨internalCode base r, behavior_choice_relation_forward base hr⟩

theorem source_choice_implies_behavior_choice (base : BaseCollection s)
    (hAC : ChoiceCode s) : BehaviorChoiceCode s :=
  (quotient_choice_iff_behavior_choice base).mp (internal_choice base hAC)

theorem translated_choice_iff_behavior_sentence (base : BaseCollection s) :
    Eval s (Formula.translate (internalInterpretation base).equalFormula
      (internalInterpretation base).memberFormula choiceSentence) Fin.elim0 ↔
    Eval s behaviorChoiceSentence Fin.elim0 := by
  rw [internal_formula_translation]
  have he : (fun i : Fin 0 => internalCode base (Fin.elim0 i)) = Fin.elim0 :=
    funext (fun i => Fin.elim0 i)
  rw [he, eval_choiceSentence, eval_behaviorChoiceSentence]
  exact quotient_choice_iff_behavior_choice base

theorem target_choice_on_injective_members (base : BaseCollection s)
    (hAC : ChoiceCode (internalMember base)) {a d : U}
    (hne : ∀ x, s x a → ∃ y, s y x)
    (hbound : ∀ x, s x a → Subset s x d) (hi : ParameterInjective base d) :
    ∃ r, ChoiceFunctionCode s a r := by
  obtain ⟨r, hr⟩ := (quotient_choice_iff_behavior_choice base).mp hAC a hne
  refine ⟨r, ⟨hr.1, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := hr.2.1 x hx
    refine ⟨y, hxy, ?_⟩
    intro z hxz
    apply hi z y (hbound x hx z (hr.2.2.1 x z hxz)) (hbound x hx y (hr.2.2.1 x y hxy))
    exact (internal_code_eq base z y).mpr
      (hr.2.2.2 x x z y (internalBehavior_refl base.empty x) hxz hxy)
  · intro x _ y hxy
    exact hr.2.2.1 x y hxy

#print axioms target_choice_on_injective_members
#print axioms quotient_choice_iff_behavior_choice
#print axioms behavior_choice_relation_pullback
#print axioms translated_choice_iff_behavior_sentence
end FullBridge
