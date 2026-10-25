import ScheduledUniverseChains
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem mask_end_extension_iff {w : U} {J : InternalMask s w → U → U}
    (a r t : MaskSupportedCarrier s w J) :
    EndExtensionCode (maskSupportedMember J) a r t ↔ EndExtensionCode s a.val r.val t.val := by
  constructor
  · intro h
    refine ⟨fun x hx => h.1 ⟨x, hereditary_mask_member t.property hx⟩ hx, ?_⟩
    intro x hx y
    let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member t.property hx⟩
    constructor
    · intro hxy
      let Y : MaskSupportedCarrier s w J := ⟨y, (mask_relation_components r.property hxy).2⟩
      exact (h.2 X hx Y).mp ((mask_coded_relation_iff r X Y).mpr hxy)
    · intro hyx
      let Y : MaskSupportedCarrier s w J := ⟨y, hereditary_mask_member X.property hyx⟩
      exact (mask_coded_relation_iff r X Y).mp ((h.2 X hx Y).mpr hyx)
  · intro h
    exact ⟨fun x hx => h.1 x.val hx,
      fun x hx y => (mask_coded_relation_iff r x y).trans (h.2 x.val hx y.val)⟩

theorem mask_bafa_of_supported_requests (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hs : ∀ i x, J i (J i x) = x)
    (hSolve : ∀ p, BafaRequestCode s p → HereditarilyMaskSupported s w J p →
      ∃ t a r f, OrbitGraphParameters s p t a r ∧ DecorationCode s a r f ∧ InjectiveCode s f ∧
        (∀ x, s x t → CodedRelation s f x x) ∧ HereditarilyMaskSupported s w J f) :
    BAFACode (maskSupportedMember J) := by
  intro t ht a r hG hExt hEnd
  obtain ⟨p, hp⟩ := orbit_graph_parameters_exists base t.val a.val r.val
  have hReq : BafaRequestCode s p := ⟨t.val, a.val, r.val, hp,
    (mask_transitive_iff t).mp ht, (mask_graph_iff a r).mp hG,
    (mask_graph_extensional_iff a r).mp hExt, (mask_end_extension_iff a r t).mp hEnd⟩
  have hpH := hereditary_mask_graph_parameter base hw hj hp t.property a.property r.property
  obtain ⟨t', a', r', f, hp', hf, hi, hfix, hfH⟩ := hSolve p hReq hpH
  obtain ⟨htt, haa, hrr⟩ := orbit_graph_parameters_unique hp' hp
  subst t'
  subst a'
  subst r'
  let F : MaskSupportedCarrier s w J := ⟨f, hfH⟩
  obtain ⟨T, hT, hfH', hiH, hrH⟩ := mask_realization_transitive_range base hj hs a r F hf hi
  exact ⟨T, F, hT, hfH', hiH, hrH, fun x hx => (mask_coded_relation_iff F x x).mpr (hfix x.val hx)⟩

theorem scheduled_chain_mask_bafa (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    {enum : Nat → U} (C : ScheduledUniverseChain base w enum) (henum : ∀ x, ∃ n, enum n = x) :
    BAFACode (maskSupportedMember (scheduledUniverseMap base C henum)) := by
  let K := C.codedChain base henum
  have hj : ∀ i, ElementaryMap s s (scheduledUniverseMap base C henum i) := fun i =>
    bijective_membership_elementary _ (iso_chain_map_injective (K.isoChain base i))
      (iso_chain_map_surjective (K.isoChain base i)) (iso_chain_map_members (K.isoChain base i))
  have hs : ∀ i x, scheduledUniverseMap base C henum i (scheduledUniverseMap base C henum i x) = x := by
    intro i x
    have h := coded_mask_chain_multiplication base K i i x
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (coded_mask_chain_identity base K x)
  exact mask_bafa_of_supported_requests base hw hj hs (scheduled_chain_all_supported_requests base C henum)

theorem countable_bafa_scheduled_mask_action (base : BaseCollection s) (hBAFA : BAFACode s)
    {z w : U} (hw : OmegaCode s z w) (P : CodedMaskAction base w)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ i j x, J (internalMaskMul base i j) x = J i (J j x)) ∧
      (∀ i x y, CodedRelation s (P.maps i) x y → J i x = y) ∧
      (∀ d, ∃ t, TransitiveCode s t ∧ Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) ∧
      BAFACode (maskSupportedMember J) := by
  obtain ⟨A, hA⟩ := joint_universe_state_exists base hBAFA P enum henum
  obtain ⟨C, hC⟩ := scheduled_universe_chain_exists base hBAFA hw A enum henum
  let K := C.codedChain base henum
  refine ⟨scheduledUniverseMap base C henum, ?_, coded_mask_chain_identity base K,
    coded_mask_chain_multiplication base K, ?_, coded_mask_chain_transitive_joint_covers base K,
    scheduled_chain_mask_bafa base hw C henum⟩
  · intro i
    exact ⟨bijective_membership_elementary _ (iso_chain_map_injective (K.isoChain base i))
      (iso_chain_map_surjective (K.isoChain base i)) (iso_chain_map_members (K.isoChain base i)),
      iso_chain_map_surjective (K.isoChain base i), iso_chain_map_local (K.isoChain base i)⟩
  · intro i x y hxy
    apply iso_chain_map_value (K.isoChain base i)
    refine ⟨0, ?_⟩
    change CodedRelation s ((C.stage 0).retained.maps i) x y
    rw [hC, hA]
    exact hxy

#print axioms countable_bafa_scheduled_mask_action
end FullBridge
