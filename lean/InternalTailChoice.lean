import InternalTailSupport
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem choice_range_row_unique (base : BaseCollection s) {w f L c y z : U}
    (P : InternalQuinePairs s w) (hf : ChoiceFunctionCode s P.family f)
    (hL : CodedImageSet s f P.family L) (hc : s c P.family)
    (hyc : s y c) (hzc : s z c) (hyL : s y L) (hzL : s z L) : y = z := by
  obtain ⟨b, hb, hby⟩ := (hL y).mp hyL
  obtain ⟨d, hd, hdz⟩ := (hL z).mp hzL
  have hbc := internal_pair_family_disjoint P base hb hc (hf.2 b hb y hby) hyc
  have hdc := internal_pair_family_disjoint P base hd hc (hf.2 d hd z hdz) hzc
  subst b
  subst d
  exact coded_function_value_unique hf.1 hby hdz

theorem choice_range_row_unbalanced (base : BaseCollection s) {w f L i l r : U}
    (P : InternalQuinePairs s w) (hf : ChoiceFunctionCode s P.family f)
    (hL : CodedImageSet s f P.family L)
    (hl : CodedRelation s P.leftCode i l) (hr : CodedRelation s P.rightCode i r) :
    ¬ (s l L ↔ s r L) := by
  intro he
  obtain ⟨c, hp⟩ := base.pairing l r
  have hc := (P.members c).mpr ⟨i, l, r, coded_function_domain P.leftFunction hl, hl, hr, hp⟩
  obtain ⟨y, hcy, _⟩ := hf.1.2 c hc
  have hyc := hf.2 c hc y hcy
  have hyL := (hL y).mpr ⟨c, hc, hcy⟩
  have hboth : s l L ∧ s r L := by
    rcases (hp y).mp hyc with hyl | hyr
    · have hlL := hyl ▸ hyL
      exact ⟨hlL, he.mp hlL⟩
    · have hrL := hyr ▸ hyL
      exact ⟨he.mpr hrL, hrL⟩
  exact internal_quine_pair_distinct P hl hr
    (choice_range_row_unique base P hf hL hc ((hp l).mpr (Or.inl rfl))
      ((hp r).mpr (Or.inr rfl)) hboth.1 hboth.2)

/-- Internally bounded support still excludes the range of every full
    family selector, even when the proposed bound is nonstandard. -/
theorem internal_tail_excludes_choice_range (base : BaseCollection s) {z w f L : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w)
    (hf : ChoiceFunctionCode s P.family f) (hL : CodedImageSet s f P.family L) :
    ¬ InternallyBoundedRowSupport s w P.leftCode P.rightCode L := by
  rintro ⟨N, hN, htail⟩
  obtain ⟨l, hl, _⟩ := P.leftFunction.2 N hN
  obtain ⟨r, hr, _⟩ := P.rightFunction.2 N hN
  exact choice_range_row_unbalanced base P hf hL hl hr
    (htail N hN (internal_omega_members_transitive_irreflexive base hw N hN).2 l r hl hr)

theorem internal_tail_full_left_range_excluded (base : BaseCollection s) {z w L : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w)
    (hL : CodedImageSet s P.leftCode w L) :
    ¬ InternallyBoundedRowSupport s w P.leftCode P.rightCode L := by
  rintro ⟨N, hN, htail⟩
  obtain ⟨l, hl, _⟩ := P.leftFunction.2 N hN
  obtain ⟨r, hr, _⟩ := P.rightFunction.2 N hN
  have hlL := (hL l).mpr ⟨N, hN, hl⟩
  have hrL := (htail N hN (internal_omega_members_transitive_irreflexive base hw N hN).2 l r hl hr).mp hlL
  obtain ⟨i, _, hi⟩ := (hL r).mp hrL
  exact P.disjoint i N r hi hr

#print axioms internal_tail_excludes_choice_range
end FullBridge
