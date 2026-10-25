import MaskedLabelActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Free variables [output,input,leftCode,rightCode,mask]. -/
def maskedLabelFormula : Formula 5 :=
  .ex (.ex (.ex (.conj (relatedFormula 5 2 1) (.conj (relatedFormula 6 2 0)
    (.conj ((Formula.equal 4 1).disj (.equal 4 0))
      ((Formula.conj (.member 2 7) (quineSwapFormula 1 0 4 3)).disj
        (.conj (.impl (.member 2 7) .bottom) (.equal 3 4))))))))

theorem eval_maskedLabelFormula (base : BaseCollection s) {w d : U}
    (P : InternalQuinePairs s w) (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c)
    (mask : U) {x : U} (hx : s x d) (y : U) :
    Eval s maskedLabelFormula (cons y (cons x (cons P.leftCode (cons P.rightCode (cons mask Fin.elim0))))) ↔
      y = maskedLabelAction P mask x := by
  classical
  let v := cons y (cons x (cons P.leftCode (cons P.rightCode (cons mask Fin.elim0))))
  simp only [maskedLabelFormula, Eval, eval_relatedFormula, eval_disj]
  change (∃ i l r, CodedRelation s P.leftCode i l ∧ CodedRelation s P.rightCode i r ∧
    (x = l ∨ x = r) ∧ ((s i mask ∧ Eval s (quineSwapFormula 1 0 4 3) (cons r (cons l (cons i v)))) ∨
      (¬s i mask ∧ y = x))) ↔ y = maskedLabelAction P mask x
  constructor
  · rintro ⟨i, l, r, hl, hr, hside, hstep⟩
    have ha := masked_label_action_value base P mask hl hr hside
    rcases hstep with ⟨hi, hflip⟩ | ⟨hi, he⟩
    · rw [if_pos hi] at ha
      have he := (eval_quineSwapFormula (s := s) 1 0 4 3 (cons r (cons l (cons i v)))
        (internal_quine_pair_distinct P hl hr)).mp hflip
      exact he.trans ha.symm
    · rw [if_neg hi] at ha
      exact he.trans ha.symm
  · intro hy
    obtain ⟨c, hc, hxc⟩ := (hd x).mp hx
    obtain ⟨i, l, r, _, hl, hr, hp⟩ := (P.members c).mp hc
    have hside := (hp x).mp hxc
    have ha := masked_label_action_value base P mask hl hr hside
    refine ⟨i, l, r, hl, hr, hside, ?_⟩
    by_cases hi : s i mask
    · rw [if_pos hi] at ha
      exact Or.inl ⟨hi, (eval_quineSwapFormula (s := s) 1 0 4 3 (cons r (cons l (cons i v)))
        (internal_quine_pair_distinct P hl hr)).mpr (hy.trans ha)⟩
    · rw [if_neg hi] at ha
      exact Or.inr ⟨hi, hy.trans ha⟩

/-- Arbitrarily large masks have actual source action graphs on the full
    internal label domain; no finite list of rows is used. -/
theorem masked_label_action_code (base : BaseCollection s) {w d : U}
    (P : InternalQuinePairs s w) (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c) (mask : U) :
    ∃ f, FunctionCode s d f ∧ ∀ x y,
      CodedRelation s f x y ↔ s x d ∧ y = maskedLabelAction P mask x := by
  obtain ⟨f, hG, hrel⟩ := normalized_relation_comprehension base maskedLabelFormula
    (cons P.leftCode (cons P.rightCode (cons mask Fin.elim0))) d
  have hr : ∀ x y, CodedRelation s f x y ↔ s x d ∧ y = maskedLabelAction P mask x := by
    intro x y
    constructor
    · intro h
      obtain ⟨hx, _, hp⟩ := (hrel x y).mp h
      exact ⟨hx, (eval_maskedLabelFormula base P hd mask hx y).mp hp⟩
    · rintro ⟨hx, rfl⟩
      exact (hrel x _).mpr ⟨hx, masked_label_action_mem base P hd mask hx,
        (eval_maskedLabelFormula base P hd mask hx _).mpr rfl⟩
  refine ⟨f, ⟨?_, ?_⟩, hr⟩
  · intro p hp
    obtain ⟨x, y, hx, _, hxy⟩ := hG p hp
    exact ⟨x, y, hx, hxy⟩
  · intro x hx
    exact ⟨_, (hr x _).mpr ⟨hx, rfl⟩, fun y hy => ((hr x y).mp hy).2⟩

#print axioms masked_label_action_code
end FullBridge
