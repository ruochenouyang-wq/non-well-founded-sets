import CoveredMaskPowers
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem covered_mask_end_extension_iff {w : U} {J : InternalMask s w → U → U}
    (a r t : CoveredMaskCarrier s w J) :
    EndExtensionCode (coveredMaskMember J) a r t ↔ EndExtensionCode s a.val r.val t.val := by
  constructor
  · intro h
    refine ⟨fun x hx => h.1 ⟨x, internal_mask_covered_member t.property hx⟩ hx, ?_⟩
    intro x hx y
    let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member t.property hx⟩
    constructor
    · intro hxy
      let Y : CoveredMaskCarrier s w J := ⟨y, (covered_mask_relation_components r.property hxy).2⟩
      exact (h.2 X hx Y).mp ((covered_mask_coded_relation_iff r X Y).mpr hxy)
    · intro hyx
      let Y : CoveredMaskCarrier s w J := ⟨y, internal_mask_covered_member X.property hyx⟩
      exact (covered_mask_coded_relation_iff r X Y).mp ((h.2 X hx Y).mpr hyx)
  · intro h
    exact ⟨fun x hx => h.1 x.val hx,
      fun x hx y => (covered_mask_coded_relation_iff r x y).trans (h.2 x.val hx y.val)⟩

/-- Full BAFA is inherited by the internally covered carrier, using the
    actual covered solution function and transitive range, not just its values. -/
theorem covered_mask_bafa (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hs : ∀ i x, J i (J i x) = x) (hB : BAFACode (maskSupportedMember J)) :
    BAFACode (coveredMaskMember J) := by
  intro t ht a r hG hE hEnd
  let tH := coveredMaskToH t
  let aH := coveredMaskToH a
  let rH := coveredMaskToH r
  obtain ⟨T, f, hT, hf, hi, hr, hfix, hfc, hTc, _⟩ :=
    mask_bafa_covered_witnesses base hj hs hB tH aH rH
      ((mask_transitive_iff tH).mpr ((covered_mask_transitive_iff t).mp ht))
      ((mask_graph_iff aH rH).mpr ((covered_mask_graph_iff a r).mp hG))
      ((mask_graph_extensional_iff aH rH).mpr ((covered_mask_graph_extensional_iff a r).mp hE))
      ((mask_end_extension_iff aH rH tH).mpr ((covered_mask_end_extension_iff a r t).mp hEnd)) a.property
  let TC : CoveredMaskCarrier s w J := ⟨T.val, hTc⟩
  let FC : CoveredMaskCarrier s w J := ⟨f.val, hfc⟩
  refine ⟨TC, FC, (covered_mask_transitive_iff TC).mpr ((mask_transitive_iff T).mp hT),
    (covered_mask_decoration_iff a r FC).mpr ((mask_decoration_iff aH rH f).mp hf),
    (covered_mask_injective_iff FC).mpr ((mask_injective_iff f).mp hi),
    (covered_mask_range_iff a FC TC).mpr ((mask_range_iff aH f T).mp hr), ?_⟩
  intro x hx
  exact (covered_mask_coded_relation_iff FC x x).mpr
    ((mask_coded_relation_iff f (coveredMaskToH x) (coveredMaskToH x)).mp (hfix (coveredMaskToH x) hx))

#print axioms covered_mask_bafa
end FullBridge
