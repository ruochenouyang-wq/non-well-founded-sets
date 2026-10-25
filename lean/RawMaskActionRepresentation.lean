import RawMaskActionSyntax
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem action_family_point_iff (base : BaseCollection s) {w x y : U}
    (A : CodedMaskAction base w) (i : InternalMask s w) :
    (∃ f, CodedRelation s A.family i.val f ∧ CodedRelation s f x y) ↔ CodedRelation s (A.maps i) x y := by
  constructor
  · rintro ⟨f, hif, hxy⟩
    exact (coded_function_value_unique A.familyFunction hif (A.mapCodes i)) ▸ hxy
  · intro hxy
    exact ⟨A.maps i, A.mapCodes i, hxy⟩

theorem coded_mask_action_raw (base : BaseCollection s) {w : U} (A : CodedMaskAction base w) :
    RawMaskAction s w A.domain A.masks A.family := by
  refine ⟨A.transitive, A.maskMembers, A.familyFunction, ?_, ?_, ?_⟩
  · intro i f hif
    let I : InternalMask s w := ⟨i, (A.maskMembers i).mp (coded_function_domain A.familyFunction hif)⟩
    exact (coded_function_value_unique A.familyFunction hif (A.mapCodes I)).symm ▸ A.iso I
  · intro e he f hef x y hxy
    have heq : e = (internalMaskOne base w).val := base.extensional e _
      (fun z => iff_of_false (he z) (internal_mask_one_mem base w z))
    have hf := coded_function_value_unique A.familyFunction (heq ▸ hef) (A.mapCodes (internalMaskOne base w))
    exact A.one x y (hf ▸ hxy)
  · intro a b c ha hb hxor f g h haf hbg hch
    let I : InternalMask s w := ⟨a, (A.maskMembers a).mp ha⟩
    let B : InternalMask s w := ⟨b, (A.maskMembers b).mp hb⟩
    have hc : c = (internalMaskMul base I B).val := (mask_xor_iff_mul base I B).mp hxor
    have hf := coded_function_value_unique A.familyFunction haf (A.mapCodes I)
    have hg := coded_function_value_unique A.familyFunction hbg (A.mapCodes B)
    have hh := coded_function_value_unique A.familyFunction (hc ▸ hch) (A.mapCodes (internalMaskMul base I B))
    rw [hf, hg, hh]
    exact A.mul I B

/-- Build the action record from only four actual source objects and their
    first-order laws. The selected maps are the values of the existing K. -/
theorem raw_mask_action_record (base : BaseCollection s) {w D G K : U}
    (h : RawMaskAction s w D G K) :
    ∃ A : CodedMaskAction base w, A.domain = D ∧ A.masks = G ∧ A.family = K := by
  classical
  obtain ⟨hD, hG, hK, hIso, hOne, hMul⟩ := h
  let maps : InternalMask s w → U := fun i => Classical.choose (hK.2 i.val ((hG i.val).mpr i.property))
  have hcodes : ∀ i, CodedRelation s K i.val (maps i) := fun i =>
    (Classical.choose_spec (hK.2 i.val ((hG i.val).mpr i.property))).1
  have hone : ∀ x y, CodedRelation s (maps (internalMaskOne base w)) x y → x = y :=
    hOne (internalMaskOne base w).val (internal_mask_one_mem base w) _ (hcodes _)
  have hmul : ∀ a b x z, CodedRelation s (maps (internalMaskMul base a b)) x z ↔
      ∃ y, CodedRelation s (maps b) x y ∧ CodedRelation s (maps a) y z := by
    intro a b
    exact hMul a.val b.val (internalMaskMul base a b).val ((hG a.val).mpr a.property)
      ((hG b.val).mpr b.property) ((mask_xor_iff_mul base a b).mpr rfl)
      (maps a) (maps b) (maps (internalMaskMul base a b)) (hcodes a) (hcodes b) (hcodes _)
  exact ⟨⟨D, hD, G, hG, K, hK, maps, hcodes, fun i => hIso i.val _ (hcodes i), hone, hmul⟩,
    rfl, rfl, rfl⟩

theorem raw_mask_action_iff_record (base : BaseCollection s) {w D G K : U} :
    RawMaskAction s w D G K ↔ ∃ A : CodedMaskAction base w, A.domain = D ∧ A.masks = G ∧ A.family = K := by
  refine ⟨raw_mask_action_record base, ?_⟩
  rintro ⟨A, rfl, rfl, rfl⟩
  exact coded_mask_action_raw base A

#print axioms raw_mask_action_iff_record
end FullBridge
