import MaskCarrierSchemes
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop} {w : U} {J : InternalMask s w → U → U}

theorem mask_pair_iff (p x y : MaskSupportedCarrier s w J) :
    IsPair (maskSupportedMember J) p x y ↔ IsPair s p.val x.val y.val := by
  constructor
  · intro hp z
    constructor
    · intro hz
      exact ((hp ⟨z, hereditary_mask_member p.property hz⟩).mp hz).elim
        (fun h => Or.inl (congrArg Subtype.val h)) (fun h => Or.inr (congrArg Subtype.val h))
    · rintro (rfl | rfl)
      · exact (hp x).mpr (Or.inl rfl)
      · exact (hp y).mpr (Or.inr rfl)
  · intro hp z
    exact (hp z.val).trans (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)

theorem mask_ordered_pair_iff (p x y : MaskSupportedCarrier s w J) :
    IsOrderedPair (maskSupportedMember J) p x y ↔ IsOrderedPair s p.val x.val y.val := by
  constructor
  · rintro ⟨a, b, ha, hb, hp⟩
    exact ⟨a.val, b.val, (mask_pair_iff a x x).mp ha, (mask_pair_iff b x y).mp hb,
      (mask_pair_iff p a b).mp hp⟩
  · rintro ⟨a, b, ha, hb, hp⟩
    let A : MaskSupportedCarrier s w J := ⟨a, hereditary_mask_member p.property ((hp a).mpr (Or.inl rfl))⟩
    let B : MaskSupportedCarrier s w J := ⟨b, hereditary_mask_member p.property ((hp b).mpr (Or.inr rfl))⟩
    exact ⟨A, B, (mask_pair_iff A x x).mpr ha, (mask_pair_iff B x y).mpr hb,
      (mask_pair_iff p A B).mpr hp⟩

theorem mask_coded_relation_iff (f x y : MaskSupportedCarrier s w J) :
    CodedRelation (maskSupportedMember J) f x y ↔ CodedRelation s f.val x.val y.val := by
  constructor
  · rintro ⟨p, hp, hpxy⟩
    exact ⟨p.val, hp, (mask_ordered_pair_iff p x y).mp hpxy⟩
  · rintro ⟨p, hp, hpxy⟩
    let P : MaskSupportedCarrier s w J := ⟨p, hereditary_mask_member f.property hp⟩
    exact ⟨P, hp, (mask_ordered_pair_iff P x y).mpr hpxy⟩

theorem mask_relation_components {f x y : U} (hf : HereditarilyMaskSupported s w J f)
    (hxy : CodedRelation s f x y) :
    HereditarilyMaskSupported s w J x ∧ HereditarilyMaskSupported s w J y := by
  obtain ⟨p, hp, a, b, ha, hb, hab⟩ := hxy
  have hP := hereditary_mask_member hf hp
  have hA := hereditary_mask_member hP ((hab a).mpr (Or.inl rfl))
  have hB := hereditary_mask_member hP ((hab b).mpr (Or.inr rfl))
  exact ⟨hereditary_mask_member hA ((ha x).mpr (Or.inl rfl)),
    hereditary_mask_member hB ((hb y).mpr (Or.inr rfl))⟩

/-- Choice-function coding is absolute for this hereditary substructure.
    No Separation, PowerSet or Collection axiom in the substructure is assumed. -/
theorem mask_choice_function_ambient (a f : MaskSupportedCarrier s w J)
    (hf : ChoiceFunctionCode (maskSupportedMember J) a f) : ChoiceFunctionCode s a.val f.val := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    let P : MaskSupportedCarrier s w J := ⟨p, hereditary_mask_member f.property hp⟩
    obtain ⟨x, y, hx, hpxy⟩ := hf.1.1 P hp
    exact ⟨x.val, y.val, hx, (mask_ordered_pair_iff P x y).mp hpxy⟩
  · intro x hx
    let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member a.property hx⟩
    obtain ⟨y, hxy, hu⟩ := hf.1.2 X hx
    refine ⟨y.val, (mask_coded_relation_iff f X y).mp hxy, ?_⟩
    intro z hxz
    let Z : MaskSupportedCarrier s w J := ⟨z, (mask_relation_components f.property hxz).2⟩
    exact congrArg Subtype.val (hu Z ((mask_coded_relation_iff f X Z).mpr hxz))
  · intro x hx y hxy
    let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member a.property hx⟩
    let Y : MaskSupportedCarrier s w J := ⟨y, (mask_relation_components f.property hxy).2⟩
    exact hf.2 X hx Y ((mask_coded_relation_iff f X Y).mpr hxy)

theorem mask_carrier_not_choice (base : BaseCollection s) {z : U} (hw : OmegaCode s z w)
    (P : InternalQuinePairs s w) (hj : ∀ a, ElementaryMap s s (J a))
    (ho : ∀ a y, ∃ x, J a x = y)
    (hcore : ∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x) :
    ¬ ChoiceCode (maskSupportedMember J) := by
  intro hAC
  let F : MaskSupportedCarrier s w J := ⟨P.family, hereditary_mask_family base hw P J hj ho hcore⟩
  obtain ⟨f, hf⟩ := hAC F (by
    intro c hc
    obtain ⟨_, l, _, _, _, _, hp⟩ := (P.members c.val).mp hc
    have hl := (hp l).mpr (Or.inl rfl)
    exact ⟨⟨l, hereditary_mask_member c.property hl⟩, hl⟩)
  exact global_selector_not_mask_supported base hw P J hj ho hcore
    (mask_choice_function_ambient F f hf) (hereditary_mask_root f.property)

/-- An actual revised hereditary candidate with bounded Separation, failed
    Choice and the label domain's relative powerset. Global PowerSet,
    full Separation, Collection and BAFA are not asserted. -/
theorem countable_bafa_mask_supported_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ P : InternalQuinePairs s w, ∃ J : InternalMask s w → U → U,
      (∀ a, ElementaryMap s s (J a) ∧ (∀ y, ∃ x, J a x = y) ∧ LocallyInternalTransitiveMap s (J a)) ∧
      (∀ a b x, J a (J b x) = J b (J a x)) ∧ (∀ a x, J a (J a x) = x) ∧
      (∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x) ∧
      HereditarilyMaskSupported s w J P.family ∧
      Extensional (maskSupportedMember J) ∧ Empty (maskSupportedMember J) ∧
      Pairing (maskSupportedMember J) ∧ Union (maskSupportedMember J) ∧ Infinity (maskSupportedMember J) ∧
      BoundedSeparation (maskSupportedMember J) ∧ ¬ ChoiceCode (maskSupportedMember J) ∧
      (∀ a x, HereditarilyMaskSupported s w J (J a x) ↔ HereditarilyMaskSupported s w J x) ∧
      ∃ d : MaskSupportedCarrier s w J,
        (∀ x, s x d.val ↔ ∃ c, s c P.family ∧ s x c) ∧
        ∃ p : MaskSupportedCarrier s w J,
          (∀ x, maskSupportedMember J x p ↔ Subset (maskSupportedMember J) x d) ∧
          (∀ L, s L p.val ↔ Subset s L d.val ∧ InternallyBoundedRowSupport s w P.leftCode P.rightCode L) := by
  obtain ⟨z, w, hw⟩ := internal_omega_exists base
  obtain ⟨P⟩ := bafa_internal_quine_pairs base hB w
  obtain ⟨J, hJ, _, _, hcore, _, _, hc, hs, _⟩ := countable_bafa_internal_mask_action base hB enum henum P
  have hj : ∀ a, ElementaryMap s s (J a) := fun a => (hJ a).1
  have ho := fun a => (hJ a).2.1
  have hl := fun a => (hJ a).2.2
  refine ⟨z, w, hw, P, J, hJ, hc, hs, hcore, hereditary_mask_family base hw P J hj ho hcore,
    mask_carrier_extensional base.extensional J, mask_carrier_empty base hw J hj ho,
    mask_carrier_pairing base hw J hj, mask_carrier_union base J hj ho,
    mask_carrier_infinity base hw J hl, mask_carrier_bounded_separation base hw J hj ho,
    mask_carrier_not_choice base hw P hj ho hcore, hereditary_mask_invariant hj hc hs, ?_⟩
  obtain ⟨d, hd⟩ := base.union P.family
  obtain ⟨hD, p, hp, hformula⟩ := mask_label_domain_relative_power base hw P J hj ho hc hs hcore hd
  exact ⟨⟨d, hD⟩, hd, p, hp, hformula⟩

#print axioms countable_bafa_mask_supported_candidate
#print axioms mask_label_domain_relative_power
end FullBridge
