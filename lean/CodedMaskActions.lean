import MaskCopyTransitionSyntax
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A transitive source domain with a jointly source-coded action of the
    whole internal mask group. The displayed maps are values of one code. -/
structure CodedMaskAction (base : BaseCollection s) (w : U) where
  domain : U
  transitive : TransitiveCode s domain
  masks : U
  maskMembers : ∀ a, s a masks ↔ Subset s a w
  family : U
  familyFunction : FunctionCode s masks family
  maps : InternalMask s w → U
  mapCodes : ∀ a, CodedRelation s family a.val (maps a)
  iso : ∀ a, MembershipIsoCode s domain domain (maps a)
  one : ∀ x y, CodedRelation s (maps (internalMaskOne base w)) x y → x = y
  mul : ∀ a b x z, CodedRelation s (maps (internalMaskMul base a b)) x z ↔
    ∃ y, CodedRelation s (maps b) x y ∧ CodedRelation s (maps a) y z

noncomputable def codedMaskIsoFamily (base : BaseCollection s) {w : U} (A : CodedMaskAction base w) :
    InternalIsoFamily s A.masks A.domain where
  code := A.family
  function := A.familyFunction
  iso := by
    intro i f hif
    let a : InternalMask s w := ⟨i, (A.maskMembers i).mp (coded_function_domain A.familyFunction hif)⟩
    have he := coded_function_value_unique A.familyFunction hif (A.mapCodes a)
    exact he.symm ▸ A.iso a
  one := (internalMaskOne base w).val
  one_mem := (A.maskMembers _).mpr (internalMaskOne base w).property
  identity := by
    intro f hf x y hxy
    have he := coded_function_value_unique A.familyFunction hf (A.mapCodes (internalMaskOne base w))
    exact A.one x y (he ▸ hxy)

theorem joint_mask_coded_action (base : BaseCollection s) {w t : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t)
    (ht : TransitiveCode s t) (hj : ∀ a, ElementaryMap s s (J a))
    (hs : ∀ a x, J a (J a x) = x) (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ a b x, J (internalMaskMul base a b) x = J a (J b x)) :
    ∃ C : CodedMaskAction base w, C.domain = t ∧ C.masks = A.masks ∧ C.family = A.family ∧
      ∀ a x y, CodedRelation s (C.maps a) x y ↔ s x t ∧ J a x = y := by
  obtain ⟨F, hF, hFo⟩ := joint_mask_internal_iso_family base A hj hs hOne
  let maps : InternalMask s w → U := fun a => Classical.choose (joint_mask_graph_exists A a)
  have hcodes : ∀ a, CodedRelation s A.family a.val (maps a) := fun a =>
    (Classical.choose_spec (joint_mask_graph_exists A a)).1
  have hrel : ∀ a x y, CodedRelation s (maps a) x y ↔ s x t ∧ J a x = y :=
    fun a => (Classical.choose_spec (joint_mask_graph_exists A a)).2.2
  have hiso : ∀ a, MembershipIsoCode s t t (maps a) := fun a =>
    F.iso a.val (maps a) (hF.symm ▸ hcodes a)
  have hone : ∀ x y, CodedRelation s (maps (internalMaskOne base w)) x y → x = y := by
    intro x y hxy
    exact (hOne x).symm.trans ((hrel _ x y).mp hxy).2
  have hmul : ∀ a b x z, CodedRelation s (maps (internalMaskMul base a b)) x z ↔
      ∃ y, CodedRelation s (maps b) x y ∧ CodedRelation s (maps a) y z := by
    intro a b x z
    constructor
    · intro h
      obtain ⟨hx, hz⟩ := (hrel _ x z).mp h
      exact ⟨J b x, (hrel b x _).mpr ⟨hx, rfl⟩,
        (hrel a _ z).mpr ⟨A.stable b x hx, (hMul a b x).symm.trans hz⟩⟩
    · rintro ⟨y, hxy, hyz⟩
      obtain ⟨hx, hbx⟩ := (hrel b x y).mp hxy
      have haz := ((hrel a y z).mp hyz).2
      exact (hrel _ x z).mpr ⟨hx, (hMul a b x).trans ((congrArg (J a) hbx).trans haz)⟩
  exact ⟨⟨t, ht, A.masks, A.maskMembers, A.family, A.familyFunction, maps, hcodes, hiso, hone, hmul⟩,
    rfl, rfl, rfl, hrel⟩
end FullBridge
