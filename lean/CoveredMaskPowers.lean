import CoveredMaskSchemes
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem covered_mask_subset_iff {w : U} {J : InternalMask s w → U → U}
    (x a : CoveredMaskCarrier s w J) : Subset (coveredMaskMember J) x a ↔ Subset s x.val a.val := by
  constructor
  · intro h y hy
    exact h ⟨y, internal_mask_covered_member x.property hy⟩ hy
  · exact fun h y hy => h y.val hy

/-- The actual H powerset of a covered object is itself covered. -/
theorem mask_covered_power_trace (hp : Pairing s) (hu : Union s) {w a p : U}
    {J : InternalMask s w → U → U} (ha : InternalMaskCovered s w J a)
    (hP : HereditarilyMaskSupported s w J p)
    (hpow : ∀ x, s x p ↔ HereditarilyMaskSupported s w J x ∧ Subset s x a) :
    InternalMaskCovered s w J p := by
  obtain ⟨C, hCt, haC, hroot⟩ := ha
  obtain ⟨D, hD⟩ := binary_union_exists hp hu C p
  have hCD : Subset s C D := fun x hx => (hD x).mpr (Or.inl hx)
  have hDt : TransitiveCode s D := by
    intro x hx y hy
    rcases (hD x).mp hx with hxC | hxp
    · exact hCD y (hCt x hxC y hy)
    · exact hCD y (hCt a haC y (((hpow x).mp hxp).2 y hy))
  have hDr : ∀ x, s x D → MaskTailSupported s w J x := by
    intro x hx
    exact ((hD x).mp hx).elim (hroot x)
      (fun hxp => hereditary_mask_root (hereditary_mask_member hP hxp))
  exact mask_covered_of_supported_subset hp hu hDt hDr (hereditary_mask_root hP)
    (fun x hx => (hD x).mpr (Or.inr hx))

theorem covered_mask_power (base : BaseCollection s) {w : U} {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ T, Nonempty (JointMaskDomain s w J T) ∧ Subset s d T) :
    PowerSet (coveredMaskMember J) := by
  intro a
  obtain ⟨T, ⟨A⟩, haT⟩ := hCover a.val
  obtain ⟨p, hp, _⟩ := joint_mask_relative_power base A hj hc hs (coveredMaskToH a) haT
  have hpc := mask_covered_power_trace base.pairing base.union a.property p.property hp
  refine ⟨⟨p.val, hpc⟩, fun x => ?_⟩
  exact (hp x.val).trans ⟨fun h => (covered_mask_subset_iff x a).mpr h.2,
    fun h => ⟨internal_mask_covered_hereditary x.property, (covered_mask_subset_iff x a).mp h⟩⟩

theorem covered_mask_transitive_containment (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (x : CoveredMaskCarrier s w J) :
    ∃ T : CoveredMaskCarrier s w J, TransitiveCode (coveredMaskMember J) T ∧ coveredMaskMember J x T := by
  obtain ⟨C, hC, hCH, hxC⟩ := (internal_mask_covered_iff_H_transitive_cover base hw hj hc hs hCover).mp x.property
  let T : CoveredMaskCarrier s w J :=
    ⟨C, hereditary_transitive_internal_mask_covered base.pairing base.union hC hCH⟩
  exact ⟨T, (covered_mask_transitive_iff T).mpr hC, hxC⟩

#print axioms covered_mask_power
#print axioms covered_mask_transitive_containment
end FullBridge
