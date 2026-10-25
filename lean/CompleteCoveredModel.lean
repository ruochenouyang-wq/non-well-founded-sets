import UniversalFullCollection
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- All base axioms and both full first-order schemes, now discharged. -/
theorem universal_Hc_full_base (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (ctx : UniversalActionContext base J) (laws : CoveredCandidateLaws J) :
    BaseCollection (coveredMaskMember J) := by
  obtain ⟨he, hem, hp, hu, hpow, hi, hsep, _⟩ := laws
  have hcol := universal_Hc_full_collection base hw ctx
  exact ⟨he, hem, hp, hu, hpow, hi, collection_bounded_separation_full_separation hcol hp hu hsep, hcol⟩

/-- Conditional on an externally countable source BaseCollection+BAFA model,
    construct an actual full BaseCollection+BAFA model failing Choice.
    No source Choice or internal omega-standardness is assumed. -/
theorem countable_bafa_full_no_choice_model (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ J : InternalMask s w → U → U,
      UniversalActionContext base J ∧ BaseCollection (coveredMaskMember J) ∧
      BAFACode (coveredMaskMember J) ∧ ¬ChoiceCode (coveredMaskMember J) ∧ CoveredCandidateLaws J := by
  obtain ⟨z, w, hw, P, J, hJ, hOne, hMul, _, hCover, laws, hUniversal, _⟩ :=
    countable_bafa_universal_covered_candidate base hB enum henum
  have hs : ∀ i x, J i (J i x) = x := by
    intro i x
    have h := hMul i i x
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (hOne x)
  let ctx : UniversalActionContext base J :=
    ⟨hB, fun i => (hJ i).1, hs, hOne, hMul, hCover, hUniversal⟩
  have hbase := universal_Hc_full_base base hw ctx laws
  have hbafa := laws.2.2.2.2.2.2.2.2.1
  have hnc := laws.2.2.2.2.2.2.2.2.2.1
  exact ⟨z, w, hw, J, ctx, hbase, hbafa, hnc, laws⟩

/-- Reconnect the constructed no-choice source to the complete existing
    behavior-quotient bridge. Choice in this quotient is not asserted. -/
theorem countable_bafa_no_choice_complete_bridge (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ M : BafaModel.{u}, ¬ChoiceCode M.mem ∧ Replacement M.mem ∧
      BaseCollection M.behaviorQuotient.mem ∧ AFACode M.behaviorQuotient.mem ∧
      Replacement M.behaviorQuotient.mem := by
  obtain ⟨z, w, hw, J, _, hbase, hbafa, hnc, _⟩ := countable_bafa_full_no_choice_model base hB enum henum
  let M : BafaModel.{u} := ⟨CoveredMaskCarrier s w J, coveredMaskMember J, hbase, hbafa⟩
  exact ⟨M, hnc, collection_separation_replacement _ hbase.collection hbase.separation,
    M.behaviorQuotient.base, M.behaviorQuotient.antiFoundation, bridge_target_replacement M⟩

#print axioms countable_bafa_full_no_choice_model
#print axioms countable_bafa_no_choice_complete_bridge
end FullBridge
