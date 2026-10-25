import InternalCopyAmalgam
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem joint_mask_membership_amalgam_cover (base : BaseCollection s) {w t : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t)
    (ht : TransitiveCode s t) (hj : ∀ a, ElementaryMap s s (J a))
    (hs : ∀ a x, J a (J a x) = x) (hOne : ∀ x, J (internalMaskOne base w) x = x) (x : U) :
    ∃ B, TransitiveCode s B ∧ Subset s t B ∧ s x B ∧
      ∃ F : InternalIsoFamily s A.masks t, F.code = A.family ∧
        F.one = (internalMaskOne base w).val ∧ Nonempty (InternalMembershipAmalgam s A.masks t B F) := by
  obtain ⟨a, ha, hxa⟩ := transitive_sets_cover base x
  obtain ⟨B, hB, htB, haB⟩ := transitive_sets_directed base ht ha
  obtain ⟨F, hF, hFo⟩ := joint_mask_internal_iso_family base A hj hs hOne
  exact ⟨B, hB, htB, haB x hxa, F, hF, hFo, internal_membership_amalgam base F ht hB htB⟩

theorem internal_label_domain_transitive {w d : U} (P : InternalQuinePairs s w)
    (hd : ∀ x, s x d ↔ ∃ c, s c P.family ∧ s x c) : TransitiveCode s d := by
  intro x hx y hyx
  obtain ⟨c, hc, hxc⟩ := (hd x).mp hx
  obtain ⟨i, l, r, _, hl, hr, hp⟩ := (P.members c).mp hc
  have hqx : SelfSingleton s x := by
    rcases (hp x).mp hxc with h | h
    · exact h ▸ P.leftQuine i l hl
    · exact h ▸ P.rightQuine i r hr
  exact ((hqx y).mp hyx).symm ▸ hx

/-- Actual joint internally indexed amalgams over a transitive set covering
    any prescribed source object. Group actions on the enlarged graph and
    coherent BAFA realization are subsequent proof obligations. -/
theorem countable_bafa_internal_mask_amalgams (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ P : InternalQuinePairs s w, ∃ J : InternalMask s w → U → U,
      (∀ a, ElementaryMap s s (J a) ∧ (∀ y, ∃ x, J a x = y) ∧ LocallyInternalTransitiveMap s (J a)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ a b x, J (internalMaskMul base a b) x = J a (J b x)) ∧
      (∀ a x, J a (J a x) = x) ∧
      ∃ d, (∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c) ∧
        ∃ A : JointMaskDomain s w J d, ∀ x, ∃ B,
          TransitiveCode s B ∧ Subset s d B ∧ s x B ∧
          ∃ F : InternalIsoFamily s A.masks d, F.code = A.family ∧
            F.one = (internalMaskOne base w).val ∧ Nonempty (InternalMembershipAmalgam s A.masks d B F) := by
  obtain ⟨z, w, hw⟩ := internal_omega_exists base
  obtain ⟨P⟩ := bafa_internal_quine_pairs base hB w
  obtain ⟨J, hJ, hOne, hMul, hcore, _, _, _, hs, _⟩ := countable_bafa_internal_mask_action base hB enum henum P
  obtain ⟨d, hd⟩ := base.union P.family
  obtain ⟨A⟩ := joint_mask_label_domain base P J hcore hd
  exact ⟨z, w, hw, P, J, hJ, hOne, hMul, hs, d, hd, A,
    joint_mask_membership_amalgam_cover base A (internal_label_domain_transitive P hd)
      (fun a => (hJ a).1) hs hOne⟩

#print axioms countable_bafa_internal_mask_amalgams
end FullBridge
