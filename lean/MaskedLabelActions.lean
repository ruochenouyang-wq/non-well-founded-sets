import InternalMaskGroup
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}
noncomputable local instance : DecidableRel s := fun _ _ => Classical.propDecidable _

structure LabelCoordinates {w : U} (P : InternalQuinePairs s w) (x : U) where
  index : U
  left : U
  right : U
  leftRel : CodedRelation s P.leftCode index left
  rightRel : CodedRelation s P.rightCode index right
  side : x = left ∨ x = right

theorem label_coordinates_unique (base : BaseCollection s) {w x : U}
    (P : InternalQuinePairs s w) (a b : LabelCoordinates P x) :
    a.index = b.index ∧ a.left = b.left ∧ a.right = b.right := by
  obtain ⟨c, hc⟩ := base.pairing a.left a.right
  obtain ⟨d, hd⟩ := base.pairing b.left b.right
  have hi := internal_quine_pair_rows_disjoint P a.leftRel a.rightRel b.leftRel b.rightRel
    hc hd ((hc x).mpr a.side) ((hd x).mpr b.side)
  exact ⟨hi, coded_function_value_unique P.leftFunction (hi ▸ a.leftRel) b.leftRel,
    coded_function_value_unique P.rightFunction (hi ▸ a.rightRel) b.rightRel⟩

noncomputable def maskedLabelAction {w : U} (P : InternalQuinePairs s w) (mask x : U) : U := by
  classical
  exact if h : Nonempty (LabelCoordinates P x) then
    let c := Classical.choice h
    if s c.index mask then quineSwap c.left c.right x else x
  else x

theorem masked_label_action_value (base : BaseCollection s) {w i l r x : U}
    (P : InternalQuinePairs s w) (mask : U)
    (hl : CodedRelation s P.leftCode i l) (hr : CodedRelation s P.rightCode i r)
    (hx : x = l ∨ x = r) :
    maskedLabelAction P mask x = if s i mask then quineSwap l r x else x := by
  classical
  let c : LabelCoordinates P x := ⟨i, l, r, hl, hr, hx⟩
  have hex : Nonempty (LabelCoordinates P x) := ⟨c⟩
  have he := label_coordinates_unique base P (Classical.choice hex) c
  simp only [maskedLabelAction, dif_pos hex, he.1, he.2.1, he.2.2]
  rfl

theorem masked_label_action_left (base : BaseCollection s) {w i l r : U}
    (P : InternalQuinePairs s w) (mask : U)
    (hl : CodedRelation s P.leftCode i l) (hr : CodedRelation s P.rightCode i r) :
    maskedLabelAction P mask l = if s i mask then r else l := by
  rw [masked_label_action_value base P mask hl hr (Or.inl rfl)]
  simp [quineSwap]

theorem masked_label_action_right (base : BaseCollection s) {w i l r : U}
    (P : InternalQuinePairs s w) (mask : U)
    (hl : CodedRelation s P.leftCode i l) (hr : CodedRelation s P.rightCode i r) :
    maskedLabelAction P mask r = if s i mask then l else r := by
  rw [masked_label_action_value base P mask hl hr (Or.inr rfl)]
  simp [quineSwap, Ne.symm (internal_quine_pair_distinct P hl hr)]

theorem masked_label_action_mem (base : BaseCollection s) {w d : U}
    (P : InternalQuinePairs s w) (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c)
    (mask : U) {x : U} (hx : s x d) : s (maskedLabelAction P mask x) d := by
  classical
  obtain ⟨c, hc, hxc⟩ := (hd x).mp hx
  obtain ⟨i, l, r, _, hl, hr, hp⟩ := (P.members c).mp hc
  apply (hd _).mpr
  refine ⟨c, hc, ?_⟩
  rcases (hp x).mp hxc with rfl | rfl
  · rw [masked_label_action_left base P mask hl hr]
    split <;> exact (hp _).mpr (by first | exact Or.inl rfl | exact Or.inr rfl)
  · rw [masked_label_action_right base P mask hl hr]
    split <;> exact (hp _).mpr (by first | exact Or.inl rfl | exact Or.inr rfl)

theorem masked_label_action_one (base : BaseCollection s) {w d : U}
    (P : InternalQuinePairs s w) (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c)
    {x : U} (hx : s x d) : maskedLabelAction P (internalMaskOne base w).val x = x := by
  obtain ⟨c, hc, hxc⟩ := (hd x).mp hx
  obtain ⟨i, l, r, _, hl, hr, hp⟩ := (P.members c).mp hc
  rw [masked_label_action_value base P _ hl hr ((hp x).mp hxc)]
  simp [internal_mask_one_mem]

theorem masked_label_action_mul (base : BaseCollection s) {w d : U}
    (P : InternalQuinePairs s w) (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c)
    (a b : InternalMask s w) {x : U} (hx : s x d) :
    maskedLabelAction P (internalMaskMul base a b).val x =
      maskedLabelAction P a.val (maskedLabelAction P b.val x) := by
  classical
  obtain ⟨c, hc, hxc⟩ := (hd x).mp hx
  obtain ⟨i, l, r, _, hl, hr, hp⟩ := (P.members c).mp hc
  rcases (hp x).mp hxc with rfl | rfl <;>
    by_cases ha : s i a.val <;> by_cases hb : s i b.val <;>
    simp [masked_label_action_left base P _ hl hr, masked_label_action_right base P _ hl hr,
      internal_mask_mul_mem, ha, hb]

theorem masked_label_action_involutive (base : BaseCollection s) {w d : U}
    (P : InternalQuinePairs s w) (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c)
    (a : InternalMask s w) {x : U} (hx : s x d) :
    maskedLabelAction P a.val (maskedLabelAction P a.val x) = x := by
  rw [← masked_label_action_mul base P hd a a hx, internal_mask_mul_self]
  exact masked_label_action_one base P hd hx

#print axioms masked_label_action_mul
end FullBridge
