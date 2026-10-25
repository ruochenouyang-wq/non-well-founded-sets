import UniversalRequestSteps
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def GlobalActionCompatible (base : BaseCollection s) {w : U}
    (J : InternalMask s w → U → U) (t : U) (Q : CodedMaskAction base w) : Prop :=
  TransitiveCode s t ∧ Subset s t Q.domain ∧
  (∀ i x, s x t → s (J i x) t) ∧
  (∀ i x y, s x t → (CodedRelation s (Q.maps i) x y ↔ J i x = y))

/-- A single global action realizes every compatible source-coded action.
    The ambient witness C and function f may depend on the request. -/
def UniversalMaskRealizations (base : BaseCollection s) {w : U}
    (J : InternalMask s w → U → U) : Prop :=
  ∀ t Q, GlobalActionCompatible base J t Q →
    ∃ C : CodedMaskAction base w, ∃ f, Nonempty (CodedMaskEmbedding base Q C f) ∧
      (∀ i x y, CodedRelation s (C.maps i) x y → J i x = y) ∧
      (∀ x, s x t → CodedRelation s f x x)

theorem universal_chain_realizations (base : BaseCollection s) {w : U} {enum : Nat → U}
    (C : UniversalUniverseChain base w enum) (henum : ∀ x, ∃ n, enum n = x) :
    UniversalMaskRealizations base
      (scheduledUniverseMap base (C.scheduled base) (recurrent_enum_onto enum henum)) := by
  let S := C.scheduled base
  let hr := recurrent_enum_onto enum henum
  let K := S.codedChain base hr
  let J := scheduledUniverseMap base S hr
  have hStage : ∀ n i x y, CodedRelation s ((C.stage n).retained.maps i) x y → J i x = y := by
    intro n i x y hxy
    exact iso_chain_map_value (K.isoChain base i) ⟨n, hxy⟩
  intro t Q htQ
  obtain ⟨ht, hsubQ, hstable, hag⟩ := htQ
  obtain ⟨p, hcode⟩ := action_request_code_exists base t Q
  obtain ⟨n, htn⟩ := K.covers t
  obtain ⟨m, hnm, hmp⟩ := recurrent_enum_cofinal enum henum p n
  have htm : s t (C.stage m).retained.domain :=
    (covering_chain_mono (K.isoChain base (internalMaskOne base w)) hnm).1 t htn
  have htP : Subset s t (C.stage m).retained.domain :=
    fun x hx => (C.stage m).retained.transitive t htm x hx
  have hcompat : ActionRequestCompatible base (C.stage m).retained Q t := by
    refine ⟨ht, htP, hsubQ, ?_, ?_⟩
    · intro i x y hx hxy
      exact (hStage m i x y hxy) ▸ hstable i x hx
    · intro i x y hx
      refine ⟨fun hxy => (hag i x y hx).mpr (hStage m i x y hxy), ?_⟩
      intro hxy
      exact (coded_action_global_agreement base (C.stage m).retained (hStage m) i x y).mpr
        ⟨htP x hx, (hag i x y hx).mp hxy⟩
  have hseal := (C.step m).2
  rw [hmp] at hseal
  obtain ⟨f, hE, hfix⟩ := hseal t Q hcode hcompat
  exact ⟨(C.stage (m+1)).retained, f, hE, hStage (m+1), hfix⟩

/-- The same global action retains the original scheduled BAFA theorem. -/
theorem countable_bafa_universal_mask_action (base : BaseCollection s) (hBAFA : BAFACode s)
    {z w : U} (hw : OmegaCode s z w) (P : CodedMaskAction base w)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ i j x, J (internalMaskMul base i j) x = J i (J j x)) ∧
      (∀ i x y, CodedRelation s (P.maps i) x y → J i x = y) ∧
      (∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T) ∧
      BAFACode (maskSupportedMember J) ∧ UniversalMaskRealizations base J := by
  obtain ⟨A, hA⟩ := joint_universe_state_exists base hBAFA P enum henum
  obtain ⟨C, hC⟩ := universal_universe_chain_exists base hBAFA hw A enum henum
  let S := C.scheduled base
  let hr := recurrent_enum_onto enum henum
  let K := S.codedChain base hr
  refine ⟨scheduledUniverseMap base S hr, ?_, coded_mask_chain_identity base K,
    coded_mask_chain_multiplication base K, ?_, coded_mask_chain_transitive_joint_covers base K,
    scheduled_chain_mask_bafa base hw S hr, universal_chain_realizations base C henum⟩
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

/-- Coverage is reflected exactly for all requests in this one global J. -/
theorem universal_mask_realizations_covered (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (h : UniversalMaskRealizations base J)
    (t : U) (Q : CodedMaskAction base w) (hcomp : GlobalActionCompatible base J t Q) :
    ∃ C : CodedMaskAction base w, ∃ f, Nonempty (CodedMaskEmbedding base Q C f) ∧
      (∀ i x y, CodedRelation s (C.maps i) x y → J i x = y) ∧
      (∀ x, s x t → CodedRelation s f x x) ∧
      ∀ x X, CodedRelation s f x X → (ActionCovered base Q x ↔ InternalMaskCovered s w J X) := by
  obtain ⟨C, f, ⟨E⟩, hJ, hfix⟩ := h t Q hcomp
  exact ⟨C, f, ⟨E⟩, hJ, hfix, fun x X hxX =>
    (coded_mask_embedding_cover_iff base E hxX).trans
      (action_covered_iff_global base C (coded_action_global_agreement base C hJ)
        (coded_mask_embedding_value base E hxX))⟩

#print axioms countable_bafa_universal_mask_action
end FullBridge
