import ScheduledCoveredRealizations
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop} {w : U} {J : InternalMask s w → U → U}

def CoveredMaskCarrier (s : U → U → Prop) (w : U) (J : InternalMask s w → U → U) :=
  {x : U // InternalMaskCovered s w J x}

def coveredMaskMember {w : U} (J : InternalMask s w → U → U)
    (x y : CoveredMaskCarrier s w J) : Prop := s x.val y.val

def coveredMaskToH {w : U} {J : InternalMask s w → U → U}
    (x : CoveredMaskCarrier s w J) : MaskSupportedCarrier s w J :=
  ⟨x.val, internal_mask_covered_hereditary x.property⟩

theorem covered_mask_pair_iff (p x y : CoveredMaskCarrier s w J) :
    IsPair (coveredMaskMember J) p x y ↔ IsPair s p.val x.val y.val := by
  constructor
  · intro hp z
    constructor
    · intro hz
      exact ((hp ⟨z, internal_mask_covered_member p.property hz⟩).mp hz).elim
        (fun h => Or.inl (congrArg Subtype.val h)) (fun h => Or.inr (congrArg Subtype.val h))
    · rintro (rfl | rfl)
      · exact (hp x).mpr (Or.inl rfl)
      · exact (hp y).mpr (Or.inr rfl)
  · intro hp z
    exact (hp z.val).trans (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)

theorem covered_mask_ordered_pair_iff (p x y : CoveredMaskCarrier s w J) :
    IsOrderedPair (coveredMaskMember J) p x y ↔ IsOrderedPair s p.val x.val y.val := by
  constructor
  · rintro ⟨a, b, ha, hb, hp⟩
    exact ⟨a.val, b.val, (covered_mask_pair_iff a x x).mp ha, (covered_mask_pair_iff b x y).mp hb,
      (covered_mask_pair_iff p a b).mp hp⟩
  · rintro ⟨a, b, ha, hb, hp⟩
    let A : CoveredMaskCarrier s w J := ⟨a, internal_mask_covered_member p.property ((hp a).mpr (Or.inl rfl))⟩
    let B : CoveredMaskCarrier s w J := ⟨b, internal_mask_covered_member p.property ((hp b).mpr (Or.inr rfl))⟩
    exact ⟨A, B, (covered_mask_pair_iff A x x).mpr ha, (covered_mask_pair_iff B x y).mpr hb,
      (covered_mask_pair_iff p A B).mpr hp⟩

theorem covered_mask_coded_relation_iff (f x y : CoveredMaskCarrier s w J) :
    CodedRelation (coveredMaskMember J) f x y ↔ CodedRelation s f.val x.val y.val := by
  constructor
  · rintro ⟨p, hp, hpxy⟩
    exact ⟨p.val, hp, (covered_mask_ordered_pair_iff p x y).mp hpxy⟩
  · rintro ⟨p, hp, hpxy⟩
    let P : CoveredMaskCarrier s w J := ⟨p, internal_mask_covered_member f.property hp⟩
    exact ⟨P, hp, (covered_mask_ordered_pair_iff P x y).mpr hpxy⟩

theorem covered_mask_relation_components {f x y : U} (hf : InternalMaskCovered s w J f)
    (hxy : CodedRelation s f x y) :
    InternalMaskCovered s w J x ∧ InternalMaskCovered s w J y := by
  obtain ⟨p, hp, a, b, ha, hb, hab⟩ := hxy
  have hP := internal_mask_covered_member hf hp
  have hA := internal_mask_covered_member hP ((hab a).mpr (Or.inl rfl))
  have hB := internal_mask_covered_member hP ((hab b).mpr (Or.inr rfl))
  exact ⟨internal_mask_covered_member hA ((ha x).mpr (Or.inl rfl)),
    internal_mask_covered_member hB ((hb y).mpr (Or.inr rfl))⟩

/-- Choice-function coding is absolute for this hereditary substructure.
    No Separation, PowerSet or Collection axiom in the substructure is assumed. -/
theorem covered_mask_choice_function_ambient (a f : CoveredMaskCarrier s w J)
    (hf : ChoiceFunctionCode (coveredMaskMember J) a f) : ChoiceFunctionCode s a.val f.val := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    let P : CoveredMaskCarrier s w J := ⟨p, internal_mask_covered_member f.property hp⟩
    obtain ⟨x, y, hx, hpxy⟩ := hf.1.1 P hp
    exact ⟨x.val, y.val, hx, (covered_mask_ordered_pair_iff P x y).mp hpxy⟩
  · intro x hx
    let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member a.property hx⟩
    obtain ⟨y, hxy, hu⟩ := hf.1.2 X hx
    refine ⟨y.val, (covered_mask_coded_relation_iff f X y).mp hxy, ?_⟩
    intro z hxz
    let Z : CoveredMaskCarrier s w J := ⟨z, (covered_mask_relation_components f.property hxz).2⟩
    exact congrArg Subtype.val (hu Z ((covered_mask_coded_relation_iff f X Z).mpr hxz))
  · intro x hx y hxy
    let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member a.property hx⟩
    let Y : CoveredMaskCarrier s w J := ⟨y, (covered_mask_relation_components f.property hxy).2⟩
    exact hf.2 X hx Y ((covered_mask_coded_relation_iff f X Y).mpr hxy)


#print axioms covered_mask_choice_function_ambient
end FullBridge
