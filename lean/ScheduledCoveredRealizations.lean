import CoveredBafaWitnesses
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def JointCoreBafaRealizations (s : U → U → Prop) (w : U) (J : InternalMask s w → U → U) : Prop :=
  ∀ t a r : MaskSupportedCarrier s w J,
    TransitiveCode (maskSupportedMember J) t → GraphCode (maskSupportedMember J) a r →
    GraphExtensionalCode (maskSupportedMember J) a r → EndExtensionCode (maskSupportedMember J) a r t →
    InternalMaskCovered s w J a.val →
    ∃ T f : MaskSupportedCarrier s w J,
      TransitiveCode (maskSupportedMember J) T ∧ DecorationCode (maskSupportedMember J) a r f ∧
      InjectiveCode (maskSupportedMember J) f ∧ RangeCode (maskSupportedMember J) a f T ∧
      (∀ x, maskSupportedMember J x t → CodedRelation (maskSupportedMember J) f x x) ∧
      ∃ C, TransitiveCode s C ∧ HereditarilyMaskSupported s w J C ∧ InternalMaskCovered s w J C ∧
        (∀ i, J i C = C) ∧ Nonempty (JointMaskDomain s w J C) ∧ s f.val C ∧ s T.val C

theorem countable_bafa_scheduled_covered_realizations (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ J : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ i j x, J (internalMaskMul base i j) x = J i (J j x)) ∧
      (∀ d, ∃ D, TransitiveCode s D ∧ Nonempty (JointMaskDomain s w J D) ∧ Subset s d D) ∧
      Extensional (maskSupportedMember J) ∧ Empty (maskSupportedMember J) ∧
      Pairing (maskSupportedMember J) ∧ Union (maskSupportedMember J) ∧ PowerSet (maskSupportedMember J) ∧
      Infinity (maskSupportedMember J) ∧ BoundedSeparation (maskSupportedMember J) ∧
      PowerBoundedSeparation (maskSupportedMember J) ∧ BAFACode (maskSupportedMember J) ∧
      ¬ ChoiceCode (maskSupportedMember J) ∧
      (BaseCollection (maskSupportedMember J) ↔ MaskCoveredWitnessBounds s w J) ∧
      JointCoreBafaRealizations s w J := by
  obtain ⟨z, w, hw, J, hJ, hOne, hMul, hCover, he, hem, hp, hu, hpow, hi, hsep, hpsep,
    hbafa, hnc, hBase, _⟩ := countable_bafa_scheduled_internal_cores base hB enum henum
  have hj : ∀ i, ElementaryMap s s (J i) := fun i => (hJ i).1
  have hc : ∀ i j x, J i (J j x) = J j (J i x) := fun i j x =>
    group_action_preserves_commutation (internalMaskGroup base w) J hMul (internal_mask_mul_comm base i j) x
  have hs : ∀ i x, J i (J i x) = x := by
    intro i x
    have h := hMul i i x
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (hOne x)
  exact ⟨z, w, hw, J, hJ, hOne, hMul, hCover, he, hem, hp, hu, hpow, hi, hsep, hpsep, hbafa, hnc, hBase,
    mask_bafa_witnesses_in_joint_core base hw hj hc hs hCover hbafa⟩

#print axioms countable_bafa_scheduled_covered_realizations
end FullBridge
