import FiberChoice
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def CodedImageSet (s : U → U → Prop) (i x c : U) : Prop :=
  ∀ v, s v c ↔ ∃ y, s y x ∧ CodedRelation s i y v

def codedImageSetFormula {n} (i x c : Fin n) : Formula n :=
  .all ((Formula.member 0 c.succ).iffF
    (.ex (.conj (.member 0 x.succ.succ) (relatedFormula i.succ.succ 0 1))))

theorem eval_codedImageSetFormula (s : U → U → Prop) {n}
    (i x c : Fin n) (v : Fin n → U) :
    Eval s (codedImageSetFormula i x c) v ↔ CodedImageSet s (v i) (v x) (v c) := by
  simp only [codedImageSetFormula, Eval, eval_iffF, eval_relatedFormula,
    CodedImageSet, cons_zero, cons_succ]
  rfl

theorem coded_image_set_exists (base : BaseCollection s) (i x : U) :
    ∃ c, CodedImageSet s i x c := by
  obtain ⟨d, hd⟩ := codedRelation_component_bound base.union i
  obtain ⟨c, hc⟩ := base.separation 2
    (Formula.ex (.conj (.member 0 2) (relatedFormula (n := 4) 3 0 1)))
    (cons x (cons i Fin.elim0)) d
  refine ⟨c, ?_⟩
  intro v
  have h := hc v
  simp only [Eval, eval_relatedFormula] at h
  change s v c ↔ s v d ∧ ∃ y, s y x ∧ CodedRelation s i y v at h
  constructor
  · exact fun hv => (h.mp hv).2
  · rintro ⟨y, hy, hyv⟩
    exact h.mpr ⟨(hd y v hyv).2, y, hy, hyv⟩

theorem coded_image_set_family (base : BaseCollection s) (a i : U) :
    ∃ b, ∀ c, s c b ↔ ∃ x, s x a ∧ CodedImageSet s i x c := by
  obtain ⟨d, hd⟩ := codedRelation_component_bound base.union i
  obtain ⟨P, hP⟩ := base.powerset d
  obtain ⟨b, hb⟩ := base.separation 2
    (Formula.ex (.conj (.member 0 2) (codedImageSetFormula (n := 4) 3 0 1)))
    (cons a (cons i Fin.elim0)) P
  refine ⟨b, ?_⟩
  intro c
  have h := hb c
  simp only [Eval, eval_codedImageSetFormula] at h
  change s c b ↔ s c P ∧ ∃ x, s x a ∧ CodedImageSet s i x c at h
  constructor
  · exact fun hc => (h.mp hc).2
  · rintro ⟨x, hx, hc⟩
    refine h.mpr ⟨(hP c).mpr ?_, x, hx, hc⟩
    intro v hv
    obtain ⟨y, _, hyv⟩ := (hc v).mp hv
    exact (hd y v hyv).2

def injectionChoiceFormula : Formula 5 :=
  .conj (.member 1 2) (.conj (.member 0 1)
    (.ex (.ex (.conj (codedImageSetFormula 5 3 1)
      (.conj (relatedFormula 6 1 0) (relatedFormula 5 2 0))))))

theorem eval_injectionChoiceFormula (s : U → U → Prop) (y x a i k : U) :
    Eval s injectionChoiceFormula (cons y (cons x (cons a (cons i (cons k Fin.elim0))))) ↔
      s x a ∧ s y x ∧ ∃ c v, CodedImageSet s i x c ∧
        CodedRelation s k c v ∧ CodedRelation s i y v := by
  simp only [injectionChoiceFormula, Eval, eval_codedImageSetFormula, eval_relatedFormula]
  rfl

theorem choice_transports_injection (base : BaseCollection s) {a i b k : U}
    (hinj : InjectiveCode s i)
    (hb : ∀ c, s c b ↔ ∃ x, s x a ∧ CodedImageSet s i x c)
    (hk : ChoiceFunctionCode s b k) :
    ∃ f, ChoiceFunctionCode s a f := by
  obtain ⟨u, hu⟩ := base.union a
  obtain ⟨D, hD⟩ := binary_union_exists base.pairing base.union a u
  obtain ⟨f, hf⟩ := relation_comprehension_members base injectionChoiceFormula
    (cons a (cons i (cons k Fin.elim0))) D
  have hn : ∀ p, s p f → ∃ x y, s x a ∧ IsOrderedPair s p x y := by
    intro p hp
    obtain ⟨x, y, _, _, hpxy, hev⟩ := (hf p).mp hp
    exact ⟨x, y, ((eval_injectionChoiceFormula s y x a i k).mp hev).1, hpxy⟩
  have hi : ∀ x y, CodedRelation s f x y ↔ s x a ∧ s y x ∧
      ∃ c v, CodedImageSet s i x c ∧ CodedRelation s k c v ∧ CodedRelation s i y v := by
    intro x y
    constructor
    · rintro ⟨p, hp, hpxy⟩
      obtain ⟨x', y', _, _, hp', hev⟩ := (hf p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxy hp'
      exact (eval_injectionChoiceFormula s y x a i k).mp hev
    · rintro ⟨hx, hy, hw⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x y
      exact ⟨p, (hf p).mpr ⟨x, y, (hD x).mpr (Or.inl hx),
        (hD y).mpr (Or.inr ((hu y).mpr ⟨x, hx, hy⟩)), hp,
        (eval_injectionChoiceFormula s y x a i k).mpr ⟨hx, hy, hw⟩⟩, hp⟩
  refine ⟨f, ⟨hn, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨c, hc⟩ := coded_image_set_exists base i x
    have hcb := (hb c).mpr ⟨x, hx, hc⟩
    obtain ⟨v, hkcv, huniq⟩ := hk.1.2 c hcb
    obtain ⟨y, hy, hyv⟩ := (hc v).mp (hk.2 c hcb v hkcv)
    refine ⟨y, (hi x y).mpr ⟨hx, hy, c, v, hc, hkcv, hyv⟩, ?_⟩
    intro z hxz
    obtain ⟨_, _, c', w, hc', hkc'w, hzw⟩ := (hi x z).mp hxz
    have hcc : c' = c := base.extensional c' c (fun t => (hc' t).trans (hc t).symm)
    subst c'
    have hwv := huniq w hkc'w
    subst w
    exact hinj z y v hzw hyv
  · intro x _ y hxy
    exact ((hi x y).mp hxy).2.1

theorem fiber_choice_transports_injection (base : BaseCollection s)
    (hFC : FiberChoiceCode s) {a d i : U}
    (hne : ∀ x, s x a → ∃ y, s y x) (hbound : ∀ x, s x a → Subset s x d)
    (hif : FunctionCode s d i) (hinj : InjectiveCode s i)
    (hhom : ∀ y z v w, s y d → s z d → CodedRelation s i y v →
      CodedRelation s i z w → InternalBehavior s v w) :
    ∃ f, ChoiceFunctionCode s a f := by
  obtain ⟨b, hb⟩ := coded_image_set_family base a i
  have hbh : ∀ c, s c b → (∃ v, s v c) ∧ BehaviorHomogeneous s c := by
    intro c hc
    obtain ⟨x, hx, hcx⟩ := (hb c).mp hc
    constructor
    · obtain ⟨y, hy⟩ := hne x hx
      obtain ⟨v, hyv, _⟩ := hif.2 y (hbound x hx y hy)
      exact ⟨v, (hcx v).mpr ⟨y, hy, hyv⟩⟩
    · intro v w hv hw
      obtain ⟨y, hy, hyv⟩ := (hcx v).mp hv
      obtain ⟨z, hz, hzw⟩ := (hcx w).mp hw
      exact hhom y z v w (hbound x hx y hy) (hbound x hx z hz) hyv hzw
  obtain ⟨k, hk⟩ := hFC b hbh
  exact choice_transports_injection base hinj hb hk

theorem bafa_fiber_choice_implies_choice (base : BaseCollection s)
    (hBAFA : BAFACode s) (hFC : FiberChoiceCode s) : ChoiceCode s := by
  intro a hne
  obtain ⟨d, hd⟩ := base.union a
  obtain ⟨i, hif, hinj, hself⟩ := bafa_selfSingleton_family base hBAFA d
  apply fiber_choice_transports_injection base hFC hne
    (fun x hx y hy => (hd y).mpr ⟨x, hx, hy⟩) hif hinj
  intro y z v w hy hz hyv hzw
  exact (internal_code_eq base v w).mp
    (selfSingleton_same_code base (hself y v hy hyv) (hself z w hz hzw))

theorem bafa_fiber_choice_iff_choice (base : BaseCollection s) (hBAFA : BAFACode s) :
    FiberChoiceCode s ↔ ChoiceCode s := by
  constructor
  · exact bafa_fiber_choice_implies_choice base hBAFA
  · intro hAC a ha
    exact hAC a (fun c hc => (ha c hc).1)

theorem bafa_fiber_choice_implies_target_choice (base : BaseCollection s)
    (hBAFA : BAFACode s) (hFC : FiberChoiceCode s) : ChoiceCode (internalMember base) :=
  internal_choice base (bafa_fiber_choice_implies_choice base hBAFA hFC)

theorem bafa_fiber_choice_sentence_equiv (base : BaseCollection s) (hBAFA : BAFACode s) :
    Eval s fiberChoiceSentence Fin.elim0 ↔ Eval s choiceSentence Fin.elim0 := by
  rw [eval_fiberChoiceSentence, eval_choiceSentence]
  exact bafa_fiber_choice_iff_choice base hBAFA

#print axioms bafa_fiber_choice_iff_choice
#print axioms fiber_choice_transports_injection
end FullBridge
