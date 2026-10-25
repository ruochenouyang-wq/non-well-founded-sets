import HereditaryMaskSupport
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem hereditary_mask_label (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hcore : ∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x)
    {x : U} (hx : ∃ c, s c P.family ∧ s x c) : HereditarilyMaskSupported s w J x := by
  classical
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨i, l, r, hi, hl, hr, hp⟩ := (P.members c).mp hc
  obtain ⟨N, hN⟩ := successor_exists base i
  have hNw := hw.2.1.2 i hi N hN
  have hfix : MaskTailSupported s w J x := by
    refine ⟨N, hNw, fun a hdis => ?_⟩
    have hnot : ¬s i a.val := fun h => hdis i h ((hN i).mpr (Or.inr rfl))
    have h := (hcore a x ⟨c, hc, hxc⟩).trans
      (masked_label_action_value base P a.val hl hr ((hp x).mp hxc))
    rw [if_neg hnot] at h
    exact h
  apply hereditary_mask_quine (hx := hfix)
  rcases (hp x).mp hxc with rfl | rfl
  · exact P.leftQuine i _ hl
  · exact P.rightQuine i _ hr

theorem hereditary_mask_family (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hj : ∀ a, ElementaryMap s s (J a)) (ho : ∀ a y, ∃ x, J a x = y)
    (hcore : ∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x) :
    HereditarilyMaskSupported s w J P.family := by
  apply hereditary_mask_intro
  · exact ⟨z, hw.2.1.1, fun a _ => (global_mask_action_fixes_family base P J hj ho hcore a).2⟩
  · intro c hc
    apply hereditary_mask_intro
    · exact ⟨z, hw.2.1.1, fun a _ => (global_mask_action_fixes_family base P J hj ho hcore a).1 c hc⟩
    · exact fun x hx => hereditary_mask_label base hw P J hcore ⟨c, hc, hx⟩

theorem mask_label_subset_hereditary_iff (base : BaseCollection s) {z w d L : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hcore : ∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x)
    (hd : ∀ x, s x d ↔ ∃ c, s c P.family ∧ s x c) (hL : Subset s L d) :
    HereditarilyMaskSupported s w J L ↔ MaskTailSupported s w J L := by
  exact ⟨hereditary_mask_root, fun h => hereditary_mask_intro h
    (fun x hx => hereditary_mask_label base hw P J hcore ((hd x).mp (hL x hx)))⟩

theorem elementary_involution_closed_set (base : BaseCollection s) {j : U → U}
    (hj : ElementaryMap s s j) (hs : ∀ x, j (j x) = x) {L : U}
    (hL : ∀ x, s x L → s (j x) L) : j L = L := by
  apply base.extensional
  intro y
  have hm : s (j y) L ↔ s y (j L) := by
    have h := hj (Formula.member (n := 2) 0 1) (cons (j y) (cons L Fin.elim0))
    change s (j y) L ↔ s (j (j y)) (j L) at h
    simpa only [hs y] using h
  exact hm.symm.trans ⟨fun h => hs y ▸ hL (j y) h, hL y⟩

/-- Exact comparison on subsets of the label domain. All internal masks,
    including internally infinite masks, are quantified over. -/
theorem mask_label_subset_support_iff (base : BaseCollection s) {w d L : U}
    (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hj : ∀ a, ElementaryMap s s (J a)) (hs : ∀ a x, J a (J a x) = x)
    (hcore : ∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x)
    (hd : ∀ x, s x d ↔ ∃ c, s c P.family ∧ s x c) (hL : Subset s L d) :
    MaskTailSupported s w J L ↔ InternallyBoundedRowSupport s w P.leftCode P.rightCode L := by
  classical
  constructor
  · rintro ⟨N, hN, hfix⟩
    refine ⟨N, hN, ?_⟩
    intro i hi hin l r hl hr
    obtain ⟨a, ha⟩ := internal_singleton_mask_exists base hi
    have hdis : ∀ j, s j a.val → ¬s j N := fun j hj => ((ha j).mp hj).symm ▸ hin
    have hleft := (hcore a l (internal_left_label_row base P hl)).trans
      (masked_label_action_left base P a.val hl hr)
    rw [if_pos ((ha i).mpr rfl)] at hleft
    have h := hj a (Formula.member (n := 2) 0 1) (cons l (cons L Fin.elim0))
    change s l L ↔ s (J a l) (J a L) at h
    simpa only [hleft, hfix a hdis] using h
  · rintro ⟨N, hN, hbal⟩
    refine ⟨N, hN, fun a hdis => ?_⟩
    apply elementary_involution_closed_set base (hj a) (hs a)
    intro x hx
    obtain ⟨c, hc, hxc⟩ := (hd x).mp (hL x hx)
    obtain ⟨i, l, r, hi, hl, hr, hp⟩ := (P.members c).mp hc
    have haction := (hcore a x ⟨c, hc, hxc⟩).trans
      (masked_label_action_value base P a.val hl hr ((hp x).mp hxc))
    by_cases him : s i a.val
    · rw [if_pos him] at haction
      rw [haction]
      exact (quine_swap_membership_invariant_iff (internal_quine_pair_distinct P hl hr)).mpr
        (hbal i hi (hdis i him) l r hl hr) x |>.mpr hx
    · rw [if_neg him] at haction
      exact haction.symm ▸ hx

theorem mask_label_subset_exact_formula (base : BaseCollection s) {z w d L : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hj : ∀ a, ElementaryMap s s (J a)) (hs : ∀ a x, J a (J a x) = x)
    (hcore : ∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x)
    (hd : ∀ x, s x d ↔ ∃ c, s c P.family ∧ s x c) (hL : Subset s L d) :
    HereditarilyMaskSupported s w J L ↔ InternallyBoundedRowSupport s w P.leftCode P.rightCode L :=
  (mask_label_subset_hereditary_iff base hw P J hcore hd hL).trans
    (mask_label_subset_support_iff base P J hj hs hcore hd hL)
end FullBridge
