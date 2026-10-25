import CoveredMaskChoice
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Any source bound for covered objects can be absorbed into one covered
    transitive set. The source bound itself need not belong to either carrier. -/
theorem covered_mask_absorbs_source_bound (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (b : U) : ∃ C : CoveredMaskCarrier s w J, TransitiveCode (coveredMaskMember J) C ∧
      ∀ x : CoveredMaskCarrier s w J, s x.val b → coveredMaskMember J x C := by
  obtain ⟨T, hT, ⟨A⟩, hbT⟩ := hCover b
  obtain ⟨C, hm, hCt, _, hCc, _⟩ := joint_internal_mask_core_exists base hw A hT hj hc hs
  let CC : CoveredMaskCarrier s w J := ⟨C, hCc⟩
  exact ⟨CC, (covered_mask_transitive_iff CC).mpr hCt,
    fun x hx => (hm x.val).mpr ⟨hbT x.val hx, x.property⟩⟩

/-- Actual truth is evaluated in the covered carrier; the ambient source
    set may contain arbitrary additional objects. -/
def CoveredCarrierSourceBounds (s : U → U → Prop) (w : U)
    (J : InternalMask s w → U → U) : Prop :=
  ∀ n (p : Formula (n+2)) (v : Fin n → CoveredMaskCarrier s w J) (a : CoveredMaskCarrier s w J),
    (∀ x, coveredMaskMember J x a → ∃ y, Eval (coveredMaskMember J) p (cons y (cons x v))) →
    ∃ b, ∀ x, coveredMaskMember J x a → ∃ y : CoveredMaskCarrier s w J,
      s y.val b ∧ Eval (coveredMaskMember J) p (cons y (cons x v))

theorem covered_mask_collection_iff_source_bounds (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T) :
    Collection (coveredMaskMember J) ↔ CoveredCarrierSourceBounds s w J := by
  constructor
  · intro h n p v a ht
    obtain ⟨b, hb⟩ := h n p v a ht
    exact ⟨b.val, hb⟩
  · intro h n p v a ht
    obtain ⟨b, hb⟩ := h n p v a ht
    obtain ⟨C, _, hC⟩ := covered_mask_absorbs_source_bound base hw hj hc hs hCover b
    refine ⟨C, fun x hx => ?_⟩
    obtain ⟨y, hyb, hy⟩ := hb x hx
    exact ⟨y, hC y hyb, hy⟩

#print axioms covered_mask_collection_iff_source_bounds
end FullBridge
