import CoveredMaskBAFA
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem quine_pair_family_internally_covered (base : BaseCollection s) {w : U}
    (P : InternalQuinePairs s w) {J : InternalMask s w → U → U}
    (hF : HereditarilyMaskSupported s w J P.family) : InternalMaskCovered s w J P.family := by
  obtain ⟨d, hd⟩ := base.union P.family
  have hq : ∀ x, s x d → SelfSingleton s x := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := (hd x).mp hx
    obtain ⟨i, l, r, _, hl, hr, hp⟩ := (P.members c).mp hc
    rcases (hp x).mp hxc with rfl | rfl
    · exact P.leftQuine i _ hl
    · exact P.rightQuine i _ hr
  obtain ⟨C, hC⟩ := binary_union_exists base.pairing base.union d P.family
  have hCt : TransitiveCode s C := by
    intro x hx y hy
    rcases (hC x).mp hx with hxd | hxf
    · exact ((hq x hxd y).mp hy).symm ▸ hx
    · exact (hC y).mpr (Or.inl ((hd y).mpr ⟨x, hxf, hy⟩))
  have hroot : ∀ x, s x C → MaskTailSupported s w J x := by
    intro x hx
    rcases (hC x).mp hx with hxd | hxf
    · obtain ⟨c, hc, hxc⟩ := (hd x).mp hxd
      exact hereditary_mask_root (hereditary_mask_member (hereditary_mask_member hF hc) hxc)
    · exact hereditary_mask_root (hereditary_mask_member hF hxf)
  exact mask_covered_of_supported_subset base.pairing base.union hCt hroot (hereditary_mask_root hF)
    (fun x hx => (hC x).mpr (Or.inr hx))

theorem covered_mask_not_choice (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    (P : InternalQuinePairs s w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (ho : ∀ i y, ∃ x, J i x = y)
    (hcore : ∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) :
    ¬ ChoiceCode (coveredMaskMember J) := by
  intro hAC
  have hF := hereditary_mask_family base hw P J hj ho hcore
  let F : CoveredMaskCarrier s w J := ⟨P.family, quine_pair_family_internally_covered base P hF⟩
  obtain ⟨f, hf⟩ := hAC F (by
    intro c hc
    obtain ⟨_, l, _, _, _, _, hp⟩ := (P.members c.val).mp hc
    have hl := (hp l).mpr (Or.inl rfl)
    exact ⟨⟨l, internal_mask_covered_member c.property hl⟩, hl⟩)
  exact global_selector_not_mask_supported base hw P J hj ho hcore
    (covered_mask_choice_function_ambient F f hf)
    (hereditary_mask_root (internal_mask_covered_hereditary f.property))

#print axioms covered_mask_not_choice
end FullBridge
