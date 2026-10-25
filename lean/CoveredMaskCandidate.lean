import CoveredMaskCollection
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The refined carrier has all the stated axioms simultaneously. Full
    Collection (and hence BaseCollection) remains exactly a source-bound
    obligation for formulas evaluated in this refined carrier. -/
theorem countable_bafa_covered_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ J : InternalMask s w → U → U,
      Extensional (coveredMaskMember J) ∧ Empty (coveredMaskMember J) ∧
      Pairing (coveredMaskMember J) ∧ Union (coveredMaskMember J) ∧ PowerSet (coveredMaskMember J) ∧
      Infinity (coveredMaskMember J) ∧ BoundedSeparation (coveredMaskMember J) ∧
      PowerBoundedSeparation (coveredMaskMember J) ∧ BAFACode (coveredMaskMember J) ∧
      ¬ ChoiceCode (coveredMaskMember J) ∧
      (∀ x : CoveredMaskCarrier s w J, ∃ T, TransitiveCode (coveredMaskMember J) T ∧ coveredMaskMember J x T) ∧
      (∀ a, ∃ b, ∀ x, s x b ↔ s x a ∧ InternalMaskCovered s w J x) ∧
      (∀ b, ∃ C : CoveredMaskCarrier s w J, TransitiveCode (coveredMaskMember J) C ∧
        ∀ x : CoveredMaskCarrier s w J, s x.val b → coveredMaskMember J x C) ∧
      (Collection (coveredMaskMember J) ↔ CoveredCarrierSourceBounds s w J) ∧
      (BaseCollection (coveredMaskMember J) ↔ CoveredCarrierSourceBounds s w J) := by
  obtain ⟨z, w, hw, P, J, hJ, hc, hs, hcore, hCover, _, _, _, _, _, _, _, _, _, hBAFA, _⟩ :=
    countable_bafa_scheduled_no_choice_candidate base hB enum henum
  have hj : ∀ i, ElementaryMap s s (J i) := fun i => (hJ i).1
  have ho := fun i => (hJ i).2.1
  have hl := fun i => (hJ i).2.2
  have hCover' : ∀ d, ∃ T, Nonempty (JointMaskDomain s w J T) ∧ Subset s d T := by
    intro d
    obtain ⟨T, _, hT, hd⟩ := hCover d
    exact ⟨T, hT, hd⟩
  have he := covered_mask_extensional base.extensional J
  have hem := covered_mask_empty base hw J hj ho
  have hp := covered_mask_pairing base hw J hj
  have hu := covered_mask_union base J hj ho
  have hpow := covered_mask_power base hj hc hs hCover'
  have hi := covered_mask_infinity base hw J hl
  have hsep := covered_mask_bounded_separation base hw J hj ho
  have hcol := covered_mask_collection_iff_source_bounds base hw hj hc hs hCover
  have hbase : BaseCollection (coveredMaskMember J) ↔ CoveredCarrierSourceBounds s w J := by
    constructor
    · exact fun h => hcol.mp h.collection
    · intro hb
      have hC := hcol.mpr hb
      exact ⟨he, hem, hp, hu, hpow, hi,
        collection_bounded_separation_full_separation hC hp hu hsep, hC⟩
  exact ⟨z, w, hw, J, he, hem, hp, hu, hpow, hi, hsep,
    power_bounded_separation_of_bounded hp hu hpow hsep,
    covered_mask_bafa base hj hs hBAFA, covered_mask_not_choice base hw P hj ho hcore,
    covered_mask_transitive_containment base hw hj hc hs hCover,
    internal_mask_covered_trace_exists base hw hj hc hs hCover,
    covered_mask_absorbs_source_bound base hw hj hc hs hCover, hcol, hbase⟩

#print axioms countable_bafa_covered_candidate
end FullBridge
