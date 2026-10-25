import MaskedCoreActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A coherent full-universe action of every actual internal mask, not
    merely products of externally finitely many single-row flips. -/
theorem countable_bafa_internal_mask_action (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) {w : U}
    (P : InternalQuinePairs s w) :
    ∃ J : InternalMask s w → U → U,
      (∀ a, ElementaryMap s s (J a) ∧ (∀ y, ∃ x, J a x = y) ∧ LocallyInternalTransitiveMap s (J a)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ a b x, J (internalMaskMul base a b) x = J a (J b x)) ∧
      (∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x) ∧
      (∀ a b, (∀ x, J a x = J b x) → a = b) ∧
      (∀ a x, internalCode base (J a x) = internalCode base x) ∧
      (∀ a b x, J a (J b x) = J b (J a x)) ∧
      (∀ a x, J a (J a x) = x) ∧
      (∀ a d, ∃ f, FunctionCode s d f ∧ ∀ x y, CodedRelation s f x y ↔ s x d ∧ J a x = y) := by
  obtain ⟨d, hd⟩ := base.union P.family
  let E := internalMaskExhaustion base w enum henum
  obtain ⟨A, _, hA⟩ := internal_mask_fixed_core_actions base P hd E
  have hAA : GroupActionExtends (A.stage 0) (A.stage 0) := ⟨fun _ hx => hx, fun _ _ _ h => h⟩
  obtain ⟨J, hJ, hOne, hMul, _, hCore, hFaith, hq, hlocal⟩ :=
    countable_bafa_controlled_group_extension base hB A (A.stage 0) hAA enum henum
  refine ⟨J, hJ, hOne, hMul, ?_, hFaith, hq, ?_, ?_, hlocal⟩
  · intro a x hx
    obtain ⟨n, i, hi⟩ := E.covers a
    have hv := hCore n i x (maskedLabelAction P a.val x)
    rw [hi] at hv
    apply hv
    apply (hA n i x _).mpr
    rw [hi]
    exact ⟨(hd x).mpr hx, rfl⟩
  · intro a b x
    exact group_action_preserves_commutation (internalMaskGroup base w) J hMul
      (internal_mask_mul_comm base a b) x
  · intro a x
    have h := hMul a a x
    change J (internalMaskMul base a a) x = J a (J a x) at h
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (hOne x)

theorem global_mask_action_fixes_family (base : BaseCollection s) {w : U}
    (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hj : ∀ a, ElementaryMap s s (J a)) (ho : ∀ a y, ∃ x, J a x = y)
    (hcore : ∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x)
    (a : InternalMask s w) :
    (∀ c, s c P.family → J a c = c) ∧ J a P.family = P.family := by
  classical
  have hrows : ∀ c, s c P.family → J a c = c := by
    intro c hc
    obtain ⟨i, l, r, _, hl, hr, hp⟩ := (P.members c).mp hc
    have hleft := (hcore a l ⟨c, hc, (hp l).mpr (Or.inl rfl)⟩).trans (masked_label_action_left base P a.val hl hr)
    have hright := (hcore a r ⟨c, hc, (hp r).mpr (Or.inr rfl)⟩).trans (masked_label_action_right base P a.val hl hr)
    have hpair := elementary_map_pair (hj a) hp
    by_cases hi : s i a.val
    · rw [if_pos hi] at hleft hright
      rw [hleft, hright] at hpair
      exact pair_unique base.extensional hpair (fun x => (hp x).trans or_comm)
    · rw [if_neg hi] at hleft hright
      rw [hleft, hright] at hpair
      exact pair_unique base.extensional hpair hp
  exact ⟨hrows, elementary_map_fixed_members_set base (hj a) (ho a) hrows⟩

/-- Every mask containing at least one internal index moves every source
    selector for the full pair family. -/
theorem global_nonempty_mask_moves_choice (base : BaseCollection s) {w : U}
    (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hj : ∀ a, ElementaryMap s s (J a)) (ho : ∀ a y, ∃ x, J a x = y)
    (hcore : ∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x)
    (a : InternalMask s w) (hne : ∃ i, s i a.val) {f : U}
    (hf : ChoiceFunctionCode s P.family f) : J a f ≠ f := by
  classical
  obtain ⟨i, hi⟩ := hne
  obtain ⟨l, hl, _⟩ := P.leftFunction.2 i (a.property i hi)
  obtain ⟨r, hr, _⟩ := P.rightFunction.2 i (a.property i hi)
  obtain ⟨c, hp⟩ := base.pairing l r
  have hc := (P.members c).mpr ⟨i, l, r, a.property i hi, hl, hr, hp⟩
  have hleft := (hcore a l ⟨c, hc, (hp l).mpr (Or.inl rfl)⟩).trans (masked_label_action_left base P a.val hl hr)
  have hright := (hcore a r ⟨c, hc, (hp r).mpr (Or.inr rfl)⟩).trans (masked_label_action_right base P a.val hl hr)
  rw [if_pos hi] at hleft hright
  exact pair_swap_moves_internal_choice (hj a) hc hp (internal_quine_pair_distinct P hl hr)
    ((global_mask_action_fixes_family base P J hj ho hcore a).1 c hc) hleft hright hf

/-- Root support for the new global action; hereditary closure and model
    axioms are deliberately not part of this definition. -/
def MaskTailSupported (s : U → U → Prop) (w : U) (J : InternalMask s w → U → U) (x : U) : Prop :=
  ∃ N, s N w ∧ ∀ a, (∀ i, s i a.val → ¬s i N) → J a x = x

theorem internal_singleton_mask_exists (base : BaseCollection s) {w i : U} (hi : s i w) :
    ∃ a : InternalMask s w, ∀ x, s x a.val ↔ x = i := by
  obtain ⟨a, ha⟩ := base.pairing i i
  have hm : ∀ x, s x a ↔ x = i := fun x =>
    (ha x).trans ⟨fun h => h.elim id id, fun h => Or.inl h⟩
  exact ⟨⟨a, fun x hx => ((hm x).mp hx).symm ▸ hi⟩, hm⟩

theorem global_internal_prefix_mask_supported (base : BaseCollection s) {w N L : U}
    (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hj : ∀ a, ElementaryMap s s (J a)) (ho : ∀ a y, ∃ x, J a x = y)
    (hcore : ∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x)
    (hN : s N w) (hL : CodedImageSet s P.leftCode N L) : MaskTailSupported s w J L := by
  classical
  refine ⟨N, hN, fun a hdis => ?_⟩
  apply elementary_map_fixed_members_set base (hj a) (ho a)
  intro y hy
  obtain ⟨i, hi, hiy⟩ := (hL y).mp hy
  obtain ⟨r, hr, _⟩ := P.rightFunction.2 i (coded_function_domain P.leftFunction hiy)
  have hfix := (hcore a y (internal_left_label_row base P hiy)).trans
    (masked_label_action_left base P a.val hiy hr)
  rw [if_neg (fun him => hdis i him hi)] at hfix
  exact hfix

theorem global_selector_not_mask_supported (base : BaseCollection s) {z w f : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hj : ∀ a, ElementaryMap s s (J a)) (ho : ∀ a y, ∃ x, J a x = y)
    (hcore : ∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x)
    (hf : ChoiceFunctionCode s P.family f) : ¬ MaskTailSupported s w J f := by
  rintro ⟨N, hN, hfix⟩
  obtain ⟨a, ha⟩ := internal_singleton_mask_exists base hN
  have hdis : ∀ i, s i a.val → ¬s i N := by
    intro i hi
    have he := (ha i).mp hi
    rw [he]
    exact (internal_omega_members_transitive_irreflexive base hw N hN).2
  exact global_nonempty_mask_moves_choice base P J hj ho hcore a
    ⟨N, (ha N).mpr rfl⟩ hf (hfix a hdis)

#print axioms countable_bafa_internal_mask_action
#print axioms global_nonempty_mask_moves_choice
#print axioms global_selector_not_mask_supported
end FullBridge
