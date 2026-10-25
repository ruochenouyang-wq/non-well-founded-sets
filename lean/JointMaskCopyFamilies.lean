import InternalCopyFamilies
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Joint mask restrictions provide an actual internally indexed family
    of membership isomorphisms with the empty mask as identity. -/
theorem joint_mask_internal_iso_family (base : BaseCollection s) {w t : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t)
    (hj : ∀ a, ElementaryMap s s (J a)) (hs : ∀ a x, J a (J a x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x) :
    ∃ F : InternalIsoFamily s A.masks t,
      F.code = A.family ∧ F.one = (internalMaskOne base w).val := by
  have hiso : ∀ i f, CodedRelation s A.family i f → MembershipIsoCode s t t f := by
    intro i f hif
    have hi := coded_function_domain A.familyFunction hif
    let M : InternalMask s w := ⟨i, (A.maskMembers i).mp hi⟩
    obtain ⟨hf, hrel⟩ := A.graphs M f hif
    refine ⟨hf, ?_, ?_, ?_⟩
    · intro x y Z hxZ hyZ
      have he := ((hrel x Z).mp hxZ).2.trans ((hrel y Z).mp hyZ).2.symm
      exact (hs M x).symm.trans ((congrArg (J M) he).trans (hs M y))
    · intro Y
      constructor
      · intro hY
        exact ⟨J M Y, A.stable M Y hY, (hrel (J M Y) Y).mpr ⟨A.stable M Y hY, hs M Y⟩⟩
      · rintro ⟨x, hx, hxy⟩
        exact ((hrel x Y).mp hxy).2 ▸ A.stable M x hx
    · intro x y X Y hxX hyY
      have hm := hj M (Formula.member (n := 2) 0 1) (cons y (cons x Fin.elim0))
      change s y x ↔ s (J M y) (J M x) at hm
      simpa only [((hrel x X).mp hxX).2, ((hrel y Y).mp hyY).2] using hm
  have hId : ∀ f, CodedRelation s A.family (internalMaskOne base w).val f →
      ∀ x y, CodedRelation s f x y → x = y := by
    intro f hf x y hxy
    have he := (((A.graphs (internalMaskOne base w) f hf).2 x y).mp hxy).2
    exact (hOne x).symm.trans he
  exact ⟨⟨A.family, A.familyFunction, hiso, (internalMaskOne base w).val,
    (A.maskMembers _).mpr (internalMaskOne base w).property, hId⟩, rfl, rfl⟩

theorem joint_mask_copy_family_over_any_set (base : BaseCollection s) {w t B : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t)
    (hj : ∀ a, ElementaryMap s s (J a)) (hs : ∀ a x, J a (J a x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x) (htB : Subset s t B) :
    ∃ F : InternalIsoFamily s A.masks t, F.code = A.family ∧
      F.one = (internalMaskOne base w).val ∧ Nonempty (InternalCopyFamily s A.masks t B F) := by
  obtain ⟨F, hF, ho⟩ := joint_mask_internal_iso_family base A hj hs hOne
  exact ⟨F, hF, ho, internal_copy_family_exists base F htB⟩
end FullBridge
