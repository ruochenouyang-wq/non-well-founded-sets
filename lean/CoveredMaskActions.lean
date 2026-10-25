import CoveredMaskCandidate
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def coveredMaskMap {w : U} {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hc : ∀ i j x, J i (J j x) = J j (J i x))
    (hs : ∀ i x, J i (J i x) = x) (i : InternalMask s w)
    (X : CoveredMaskCarrier s w J) : CoveredMaskCarrier s w J :=
  ⟨J i X.val, (internal_mask_covered_invariant hj hc hs i X.val).mpr X.property⟩

theorem covered_mask_map_involutive {w : U} {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hc : ∀ i j x, J i (J j x) = J j (J i x))
    (hs : ∀ i x, J i (J i x) = x) (i : InternalMask s w) (X : CoveredMaskCarrier s w J) :
    coveredMaskMap hj hc hs i (coveredMaskMap hj hc hs i X) = X := Subtype.ext (hs i X.val)

theorem covered_mask_map_elementary {w : U} {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hc : ∀ i j x, J i (J j x) = J j (J i x))
    (hs : ∀ i x, J i (J i x) = x) (i : InternalMask s w) :
    ElementaryMap (coveredMaskMember J) (coveredMaskMember J) (coveredMaskMap hj hc hs i) := by
  apply bijective_membership_elementary
  · intro X Y h
    have hh := congrArg (coveredMaskMap hj hc hs i) h
    simpa only [covered_mask_map_involutive] using hh
  · intro X
    exact ⟨coveredMaskMap hj hc hs i X, covered_mask_map_involutive hj hc hs i X⟩
  · intro X Y
    exact (hj i) (Formula.member (n := 2) 0 1) (cons X.val (cons Y.val Fin.elim0))

theorem covered_mask_witness_transport {w : U} {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hc : ∀ i j x, J i (J j x) = J j (J i x))
    (hs : ∀ i x, J i (J i x) = x) {n} (p : Formula (n+2))
    (v : Fin n → CoveredMaskCarrier s w J) (x y : CoveredMaskCarrier s w J)
    (i : InternalMask s w) (hv : ∀ j, J i (v j).val = (v j).val)
    (h : Eval (coveredMaskMember J) p (cons y (cons x v))) :
    Eval (coveredMaskMember J) p
      (cons (coveredMaskMap hj hc hs i y) (cons (coveredMaskMap hj hc hs i x) v)) := by
  have he : (fun j => coveredMaskMap hj hc hs i (cons y (cons x v) j)) =
      cons (coveredMaskMap hj hc hs i y) (cons (coveredMaskMap hj hc hs i x) v) := by
    funext j
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun j => Subtype.ext (hv j)) j) j
  have ht := ((covered_mask_map_elementary hj hc hs i) p (cons y (cons x v))).mp h
  rw [he] at ht
  exact ht

/-- Existing source sets whose members are covered acquire a cover as soon
    as the set itself has root support. No collection inside Hc is used. -/
theorem covered_mask_set_of_covered_members (base : BaseCollection s) {z w b : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (hb : MaskTailSupported s w J b) (hm : ∀ x, s x b → InternalMaskCovered s w J x) :
    InternalMaskCovered s w J b := by
  obtain ⟨C, hC, hbC⟩ := covered_mask_absorbs_source_bound base hw hj hc hs hCover b
  exact mask_covered_of_supported_subset base.pairing base.union
    ((covered_mask_transitive_iff C).mp hC)
    (fun x hx => hereditary_mask_root (internal_mask_covered_hereditary (internal_mask_covered_member C.property hx))) hb
    (fun x hx => hbC ⟨x, hm x hx⟩ hx)

/-- One actual covered transitive set bounds all mask translates of every
    covered point in a prescribed source set. -/
theorem covered_mask_orbit_bound (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (b : U) : ∃ C : CoveredMaskCarrier s w J, TransitiveCode (coveredMaskMember J) C ∧
      ∀ x : CoveredMaskCarrier s w J, s x.val b → ∀ i, coveredMaskMember J (coveredMaskMap hj hc hs i x) C := by
  obtain ⟨T, hT, ⟨A⟩, hbT⟩ := hCover b
  obtain ⟨C, hm, hCt, _, hCc, _⟩ := joint_internal_mask_core_exists base hw A hT hj hc hs
  let CC : CoveredMaskCarrier s w J := ⟨C, hCc⟩
  exact ⟨CC, (covered_mask_transitive_iff CC).mpr hCt,
    fun x hx i => (hm _).mpr ⟨A.stable i x.val (hbT x.val hx),
      (internal_mask_covered_invariant hj hc hs i x.val).mpr x.property⟩⟩

#print axioms covered_mask_orbit_bound
end FullBridge
