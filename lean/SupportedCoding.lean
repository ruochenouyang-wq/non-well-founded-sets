import HereditarySupport
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop} {swap : Nat → U → U}

theorem supported_pair_iff (p x y : SupportedCarrier s swap) :
    IsPair (supportedMember swap) p x y ↔ IsPair s p.val x.val y.val := by
  constructor
  · intro hp z
    constructor
    · intro hz
      exact ((hp ⟨z, hereditary_support_member p.property hz⟩).mp hz).elim
        (fun h => Or.inl (congrArg Subtype.val h)) (fun h => Or.inr (congrArg Subtype.val h))
    · rintro (rfl | rfl)
      · exact (hp x).mpr (Or.inl rfl)
      · exact (hp y).mpr (Or.inr rfl)
  · intro hp z
    exact (hp z.val).trans (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)

theorem supported_ordered_pair_iff (p x y : SupportedCarrier s swap) :
    IsOrderedPair (supportedMember swap) p x y ↔ IsOrderedPair s p.val x.val y.val := by
  constructor
  · rintro ⟨a, b, ha, hb, hp⟩
    exact ⟨a.val, b.val, (supported_pair_iff a x x).mp ha, (supported_pair_iff b x y).mp hb,
      (supported_pair_iff p a b).mp hp⟩
  · rintro ⟨a, b, ha, hb, hp⟩
    let A : SupportedCarrier s swap := ⟨a, hereditary_support_member p.property ((hp a).mpr (Or.inl rfl))⟩
    let B : SupportedCarrier s swap := ⟨b, hereditary_support_member p.property ((hp b).mpr (Or.inr rfl))⟩
    exact ⟨A, B, (supported_pair_iff A x x).mpr ha, (supported_pair_iff B x y).mpr hb,
      (supported_pair_iff p A B).mpr hp⟩

theorem supported_coded_relation_iff (f x y : SupportedCarrier s swap) :
    CodedRelation (supportedMember swap) f x y ↔ CodedRelation s f.val x.val y.val := by
  constructor
  · rintro ⟨p, hp, hpxy⟩
    exact ⟨p.val, hp, (supported_ordered_pair_iff p x y).mp hpxy⟩
  · rintro ⟨p, hp, hpxy⟩
    let P : SupportedCarrier s swap := ⟨p, hereditary_support_member f.property hp⟩
    exact ⟨P, hp, (supported_ordered_pair_iff P x y).mpr hpxy⟩

theorem supported_relation_components {f x y : U} (hf : HereditarilyEventuallyFixed s swap f)
    (hxy : CodedRelation s f x y) :
    HereditarilyEventuallyFixed s swap x ∧ HereditarilyEventuallyFixed s swap y := by
  obtain ⟨p, hp, a, b, ha, hb, hab⟩ := hxy
  have hP := hereditary_support_member hf hp
  have hA := hereditary_support_member hP ((hab a).mpr (Or.inl rfl))
  have hB := hereditary_support_member hP ((hab b).mpr (Or.inr rfl))
  exact ⟨hereditary_support_member hA ((ha x).mpr (Or.inl rfl)),
    hereditary_support_member hB ((hb y).mpr (Or.inr rfl))⟩

/-- Choice-function coding is absolute for this hereditary substructure.
    No Separation, PowerSet or Collection axiom in the substructure is assumed. -/
theorem supported_choice_function_ambient (a f : SupportedCarrier s swap)
    (hf : ChoiceFunctionCode (supportedMember swap) a f) : ChoiceFunctionCode s a.val f.val := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    let P : SupportedCarrier s swap := ⟨p, hereditary_support_member f.property hp⟩
    obtain ⟨x, y, hx, hpxy⟩ := hf.1.1 P hp
    exact ⟨x.val, y.val, hx, (supported_ordered_pair_iff P x y).mp hpxy⟩
  · intro x hx
    let X : SupportedCarrier s swap := ⟨x, hereditary_support_member a.property hx⟩
    obtain ⟨y, hxy, hu⟩ := hf.1.2 X hx
    refine ⟨y.val, (supported_coded_relation_iff f X y).mp hxy, ?_⟩
    intro z hxz
    let Z : SupportedCarrier s swap := ⟨z, (supported_relation_components f.property hxz).2⟩
    exact congrArg Subtype.val (hu Z ((supported_coded_relation_iff f X Z).mpr hxz))
  · intro x hx y hxy
    let X : SupportedCarrier s swap := ⟨x, hereditary_support_member a.property hx⟩
    let Y : SupportedCarrier s swap := ⟨y, (supported_relation_components f.property hxy).2⟩
    exact hf.2 X hx Y ((supported_coded_relation_iff f X Y).mpr hxy)

theorem supported_carrier_choice_obstruction {a : U} (ha : HereditarilyEventuallyFixed s swap a)
    (hne : ∀ x, s x a → ∃ y, s y x)
    (hmove : ∀ n f, ChoiceFunctionCode s a f → swap n f ≠ f) :
    ¬ ChoiceCode (supportedMember (s := s) swap) := by
  intro hAC
  let A : SupportedCarrier s swap := ⟨a, ha⟩
  obtain ⟨f, hf⟩ := hAC A (by
    intro x hx
    obtain ⟨y, hy⟩ := hne x.val hx
    exact ⟨⟨y, hereditary_support_member x.property hy⟩, hy⟩)
  obtain ⟨N, hN⟩ := hereditary_support_root f.property
  exact hmove N f.val (supported_choice_function_ambient A f hf) (hN N (Nat.le_refl N))

#print axioms supported_carrier_choice_obstruction
end FullBridge
