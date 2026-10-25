import MaskTailOrbits
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The family consists of actual orbit sets, not selected representatives. -/
theorem joint_tail_orbit_family (base : BaseCollection s) {w T N a : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J T) (haT : Subset s a T) :
    ∃ F, ∀ O, s O F ↔ ∃ x, s x a ∧ TailOrbitCode s J N x O := by
  have rep := collection_separation_replacement s base.collection base.separation
  have ht : ∀ x, s x a → ∃ O,
      Eval s (tailOrbitSetFormula (n := 5) 2 3 4 1 0)
        (cons O (cons x (cons A.masks (cons A.family (cons N Fin.elim0))))) ∧
      ∀ D, Eval s (tailOrbitSetFormula (n := 5) 2 3 4 1 0)
        (cons D (cons x (cons A.masks (cons A.family (cons N Fin.elim0))))) → D = O := by
    intro x hx
    obtain ⟨O, hO⟩ := joint_tail_orbit_exists (N := N) base A (haT x hx)
    exact ⟨O, (joint_tail_orbit_set_formula A (haT x hx)).mpr hO, fun D hD =>
      base.extensional D O (fun y => ((joint_tail_orbit_set_formula A (haT x hx)).mp hD y).trans (hO y).symm)⟩
  obtain ⟨F, hF⟩ := rep 3 (tailOrbitSetFormula 2 3 4 1 0)
    (cons A.masks (cons A.family (cons N Fin.elim0))) a ht
  exact ⟨F, fun O => (hF O).trans (exists_congr (fun x => and_congr_right
    (fun hx => joint_tail_orbit_set_formula A (haT x hx))))⟩

/-- All orbit objects share the same root support N. Their elements need not
    be pointwise fixed by the tail subgroup. -/
theorem covered_tail_orbit_family (base : BaseCollection s) {z w N : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (hN : s N w) (a : CoveredMaskCarrier s w J)
    (ha : ∀ i, TailMask s N i → J i a.val = a.val) :
    ∃ F : CoveredMaskCarrier s w J,
      (∀ O : CoveredMaskCarrier s w J, coveredMaskMember J O F ↔
        ∃ x : CoveredMaskCarrier s w J, coveredMaskMember J x a ∧ TailOrbitCode s J N x.val O.val) ∧
      (∀ O, coveredMaskMember J O F → ∀ i, TailMask s N i → J i O.val = O.val) ∧
      (∀ x, coveredMaskMember J x a → ∃ O, coveredMaskMember J O F ∧ coveredMaskMember J x O) := by
  obtain ⟨T, _, ⟨A⟩, haT⟩ := hCover a.val
  obtain ⟨F, hF⟩ := joint_tail_orbit_family (N := N) base A haT
  have hOc : ∀ O, s O F → InternalMaskCovered s w J O := by
    intro O hOF
    obtain ⟨x, hx, hO⟩ := (hF O).mp hOF
    have hsub := tail_orbit_subset hj hx ha hO
    have hroot : MaskTailSupported s w J O := ⟨N, hN, tail_orbit_fixed base hj hs hMul hO⟩
    have hH := hereditary_mask_intro hroot
      (fun y hy => internal_mask_covered_hereditary (internal_mask_covered_member a.property (hsub y hy)))
    exact mask_covered_H_subset base.pairing base.union a.property hH hsub
  have hpoint : ∀ O, s O F → ∀ i, TailMask s N i → J i O = O := by
    intro O hOF i hi
    obtain ⟨_, _, hO⟩ := (hF O).mp hOF
    exact tail_orbit_fixed base hj hs hMul hO i hi
  have hFc := covered_mask_set_of_covered_members base hw hj hc hs hCover
    ⟨N, hN, fun i hi => elementary_involution_closed_set base (hj i) (hs i)
      (fun O hO => (hpoint O hO i hi).symm ▸ hO)⟩ hOc
  let FF : CoveredMaskCarrier s w J := ⟨F, hFc⟩
  refine ⟨FF, ?_, fun O hO => hpoint O.val hO, ?_⟩
  · intro O
    constructor
    · intro hO
      obtain ⟨x, hx, hCode⟩ := (hF O.val).mp hO
      exact ⟨⟨x, internal_mask_covered_member a.property hx⟩, hx, hCode⟩
    · rintro ⟨x, hx, hCode⟩
      exact (hF O.val).mpr ⟨x.val, hx, hCode⟩
  · intro x hx
    obtain ⟨O, hO⟩ := joint_tail_orbit_exists (N := N) base A (haT x.val hx)
    have hOF := (hF O).mpr ⟨x.val, hx, hO⟩
    exact ⟨⟨O, hOc O hOF⟩, hOF, tail_orbit_contains_seed base hOne hO⟩

#print axioms covered_tail_orbit_family
end FullBridge
