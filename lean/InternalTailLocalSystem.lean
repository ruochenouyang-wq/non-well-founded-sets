import InternalRowSwapFamily
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem row_swap_code_involutive {left right d i f x y z : U}
    (hf : RowSwapCode s left right d i f)
    (hxy : CodedRelation s f x y) (hyz : CodedRelation s f y z) : z = x := by
  obtain ⟨l, r, _, _, hne, _, hrel⟩ := hf
  have hy := ((hrel x y).mp hxy).2
  have hz := ((hrel y z).mp hyz).2
  exact hz.trans ((congrArg (quineSwap l r) hy).trans (quine_swap_involutive hne x))

theorem internal_pair_flips_commute {w i j l r L R : U} (P : InternalQuinePairs s w)
    (hl : CodedRelation s P.leftCode i l) (hr : CodedRelation s P.rightCode i r)
    (hL : CodedRelation s P.leftCode j L) (hR : CodedRelation s P.rightCode j R) (x : U) :
    quineSwap l r (quineSwap L R x) = quineSwap L R (quineSwap l r x) := by
  classical
  by_cases hij : i = j
  · subst j
    have hLl := coded_function_value_unique P.leftFunction hL hl
    have hRr := coded_function_value_unique P.rightFunction hR hr
    subst L
    subst R
    rfl
  · apply disjoint_quine_swaps_commute (internal_quine_pair_distinct P hl hr)
      (internal_quine_pair_distinct P hL hR)
    · intro he
      exact hij (P.leftInjective i j l hl (he.symm ▸ hL))
    · intro he
      exact P.disjoint i j l hl (he.symm ▸ hR)
    · intro he
      exact P.disjoint j i r (he.symm ▸ hL) hr
    · intro he
      exact hij (P.rightInjective i j r hr (he.symm ▸ hR))

theorem row_swap_code_preserves_set_iff {d l r f a : U}
    (hf : SwapGraphCode s d l r f) (hne : l ≠ r) (hl : s l d) :
    (∀ x y, CodedRelation s f x y → (s x a ↔ s y a)) ↔ (s l a ↔ s r a) := by
  classical
  constructor
  · intro h
    apply h l r
    exact (hf.2 l r).mpr ⟨hl, by simp [quineSwap]⟩
  · intro h x y hxy
    have he := ((hf.2 x y).mp hxy).2
    rw [he]
    exact ((quine_swap_membership_invariant_iff hne).mpr h x).symm

/-- The definable balance predicate is exactly invariance under the
    internally indexed coded local swaps beyond the internal bound. -/
theorem internal_tail_iff_coded_swap_invariance (base : BaseCollection s) {w d k N a : U}
    (P : InternalQuinePairs s w) (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c)
    (hk : FunctionCode s w k)
    (hcode : ∀ i f, CodedRelation s k i f ↔ s i w ∧ RowSwapCode s P.leftCode P.rightCode d i f) :
    RowTailBalanced s w P.leftCode P.rightCode N a ↔
      ∀ i, s i w → ¬s i N → ∀ f, CodedRelation s k i f →
        ∀ x y, CodedRelation s f x y → (s x a ↔ s y a) := by
  constructor
  · intro ht i hi hin f hif
    obtain ⟨l, r, hl, hr, hne, hf⟩ := ((hcode i f).mp hif).2
    exact (row_swap_code_preserves_set_iff hf hne
      ((hd l).mpr (internal_left_label_row base P hl))).mpr (ht i hi hin l r hl hr)
  · intro ht i hi hin l r hl hr
    obtain ⟨f, hif, _⟩ := hk.2 i hi
    obtain ⟨L, R, hL, hR, hne, hf⟩ := ((hcode i f).mp hif).2
    have hLl := coded_function_value_unique P.leftFunction hL hl
    have hRr := coded_function_value_unique P.rightFunction hR hr
    subst L
    subst R
    exact (row_swap_code_preserves_set_iff hf hne
      ((hd l).mpr (internal_left_label_row base P hl))).mp (ht i hi hin f hif)

/-- Actual internal data for the revised local route. This theorem does
    not assert a coherent full-universe action or a full symmetric model. -/
theorem bafa_internal_tail_local_system (base : BaseCollection s) (hB : BAFACode s)
    {z w : U} (hw : OmegaCode s z w) :
    ∃ P : InternalQuinePairs s w, ∃ d k p,
      (∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c) ∧
      FunctionCode s w k ∧
      (∀ i f, CodedRelation s k i f ↔ s i w ∧ RowSwapCode s P.leftCode P.rightCode d i f) ∧
      (∀ a, s a p ↔ Subset s a d ∧ InternallyBoundedRowSupport s w P.leftCode P.rightCode a) ∧
      (∀ a, s a w → ∃ L, CodedImageSet s P.leftCode a L ∧ s L p) ∧
      (∀ f L, ChoiceFunctionCode s P.family f → CodedImageSet s f P.family L → ¬s L p) ∧
      (∃ f, ChoiceFunctionCode s P.family f) := by
  obtain ⟨P⟩ := bafa_internal_quine_pairs base hB w
  obtain ⟨d, hd⟩ := base.union P.family
  obtain ⟨k, hk, hcode⟩ := internal_row_swap_family_code base P hd
  obtain ⟨p, hp⟩ := internally_supported_subsets_exist base w P.leftCode P.rightCode d
  refine ⟨P, d, k, p, hd, hk, hcode, hp, ?_, ?_, internal_quine_pairs_have_choice base P⟩
  · intro a ha
    obtain ⟨L, hL⟩ := coded_image_set_exists base P.leftCode a
    exact ⟨L, hL, (hp L).mpr ⟨left_prefix_subset_union base P hL hd,
      internal_left_prefix_row_supported P ha hL⟩⟩
  · intro f L hf hL hLp
    exact internal_tail_excludes_choice_range base hw P hf hL ((hp L).mp hLp).2

/-- The revised local support actually adds a set that the old indexed
    hereditary candidate excludes, when internal omega is nonstandard. -/
theorem internal_tail_retains_nonstandard_prefix_excluded_by_old_support
    (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    (P : InternalQuinePairs s w) (S : PairSwapSequence s P.family)
    (hidx : OmegaSwapIndexed base z P S)
    (hns : ∃ a, s a w ∧ ∀ n, a ≠ standardOmegaValue base z n) :
    ∃ a L, s a w ∧ CodedImageSet s P.leftCode a L ∧
      InternallyBoundedRowSupport s w P.leftCode P.rightCode L ∧
      ¬ HereditarilyEventuallyFixed s S.map L := by
  obtain ⟨a, ha, hns⟩ := hns
  obtain ⟨L, hL⟩ := coded_image_set_exists base P.leftCode a
  refine ⟨a, L, ha, hL, internal_left_prefix_row_supported P ha hL, ?_⟩
  intro hH
  obtain ⟨n, hn⟩ := (indexed_prefix_supported_iff_standard base hw P S hidx ha hL).mp hH
  exact hns n hn

#print axioms bafa_internal_tail_local_system
#print axioms internal_tail_retains_nonstandard_prefix_excluded_by_old_support
end FullBridge
