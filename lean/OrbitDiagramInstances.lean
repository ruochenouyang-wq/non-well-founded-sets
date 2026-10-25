import JointOrbitDiagrams
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem coded_mask_chain_transitive_joint_covers (base : BaseCollection s) {w : U}
    (C : CoveringCodedMaskChain base w) (d : U) :
    ∃ B, TransitiveCode s B ∧ Nonempty (JointMaskDomain s w (codedMaskChainMap base C) B) ∧ Subset s d B := by
  obtain ⟨n, hn⟩ := C.covers d
  exact ⟨(C.stage n).domain, (C.stage n).transitive, coded_mask_chain_joint_domain base C n,
    fun x hx => (C.stage n).transitive d hn x hx⟩

/-- One actual global action supports actual orbit diagrams for EVERY
    admissible source request. This says diagrams, not solutions or BAFA in H. -/
theorem countable_bafa_request_orbit_diagrams (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ P : InternalQuinePairs s w, ∃ J : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ i j x, J (internalMaskMul base i j) x = J i (J j x)) ∧
      (∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) ∧
      (∀ d, ∃ B, TransitiveCode s B ∧ Nonempty (JointMaskDomain s w J B) ∧ Subset s d B) ∧
      ∀ p, BafaRequestCode s p → ∃ O,
        (∀ q, s q O ↔ ∃ i : InternalMask s w, J i p = q) ∧ s p O ∧
        Nonempty (CodedOrbitDiagram base w J O) := by
  obtain ⟨z, w, hw, P, A, hd, hAr, _⟩ := countable_bafa_joint_mask_extensions base hB enum henum
  obtain ⟨C, hC⟩ := enumerated_coded_mask_chain base hB A enum henum
  let J := codedMaskChainMap base C
  have hOne : ∀ x, J (internalMaskOne base w) x = x := coded_mask_chain_identity base C
  have hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x) := coded_mask_chain_multiplication base C
  have hJ : ∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i) := by
    intro i
    exact ⟨bijective_membership_elementary _ (iso_chain_map_injective (C.isoChain base i))
      (iso_chain_map_surjective (C.isoChain base i)) (iso_chain_map_members (C.isoChain base i)),
      iso_chain_map_surjective (C.isoChain base i), iso_chain_map_local (C.isoChain base i)⟩
  have hs : ∀ i x, J i (J i x) = x := by
    intro i x
    have h := hMul i i x
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (hOne x)
  have hOld : ∀ i x y, CodedRelation s (A.maps i) x y → J i x = y := by
    intro i x y hxy
    apply iso_chain_map_value (C.isoChain base i)
    refine ⟨0, ?_⟩
    change CodedRelation s ((C.stage 0).maps i) x y
    rw [hC]
    exact hxy
  refine ⟨z, w, hw, P, J, hJ, hOne, hMul, ?_, coded_mask_chain_transitive_joint_covers base C, ?_⟩
  · intro i x hx
    exact hOld i x _ ((hAr i x _).mpr ⟨(hd x).mpr hx, rfl⟩)
  · intro p hp
    obtain ⟨n, hn⟩ := C.covers p
    obtain ⟨A'⟩ := coded_mask_chain_joint_domain base C n
    exact actual_request_orbit_diagram base A' (C.stage n).transitive
      (fun i => (hJ i).1) hs hOne hMul hn hp

theorem hereditary_mask_graph_parameter (base : BaseCollection s) {z w p t a r : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hp : OrbitGraphParameters s p t a r)
    (ht : HereditarilyMaskSupported s w J t) (ha : HereditarilyMaskSupported s w J a)
    (hr : HereditarilyMaskSupported s w J r) : HereditarilyMaskSupported s w J p := by
  obtain ⟨b, hb, hp⟩ := hp
  exact hereditary_mask_ordered_pair base hw hj ht (hereditary_mask_ordered_pair base hw hj ha hr hb) hp

theorem supported_parameter_tail_preserves_component (base : BaseCollection s)
    {z w N E p t a r : U} (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (C : OrbitDiagramComponent s N E p a r)
    (hp : OrbitGraphParameters s p t a r)
    (ht : HereditarilyMaskSupported s w J t) (ha : HereditarilyMaskSupported s w J a)
    (hr : HereditarilyMaskSupported s w J r) :
    ∃ K, s K w ∧ ∀ i, (∀ k, s k i.val → ¬s k K) → ∀ X, s X C.domain → s (J i X) C.domain := by
  obtain ⟨K, hK, hfix⟩ := hereditary_mask_root (hereditary_mask_graph_parameter base hw hj hp ht ha hr)
  exact ⟨K, hK, fun i hi => parameter_stabilizer_preserves_component base (hj i) C hp (hfix i hi)⟩

#print axioms countable_bafa_request_orbit_diagrams
#print axioms supported_parameter_tail_preserves_component
end FullBridge
