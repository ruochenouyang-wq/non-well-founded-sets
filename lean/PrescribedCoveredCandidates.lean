import CodedActionCovers
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Only the already verified axioms are bundled. Full Separation and
    Collection are deliberately not fields of this conclusion. -/
def CoveredCandidateLaws {w : U} (J : InternalMask s w → U → U) : Prop :=
  Extensional (coveredMaskMember J) ∧ Empty (coveredMaskMember J) ∧
  Pairing (coveredMaskMember J) ∧ Union (coveredMaskMember J) ∧ PowerSet (coveredMaskMember J) ∧
  Infinity (coveredMaskMember J) ∧ BoundedSeparation (coveredMaskMember J) ∧
  PowerBoundedSeparation (coveredMaskMember J) ∧ BAFACode (coveredMaskMember J) ∧
  ¬ ChoiceCode (coveredMaskMember J) ∧
  (∀ x : CoveredMaskCarrier s w J, ∃ T, TransitiveCode (coveredMaskMember J) T ∧ coveredMaskMember J x T)

theorem coded_action_global_agreement (base : BaseCollection s) {w : U} (A : CodedMaskAction base w)
    {J : InternalMask s w → U → U}
    (hJ : ∀ i x y, CodedRelation s (A.maps i) x y → J i x = y) :
    ∀ i x y, CodedRelation s (A.maps i) x y ↔ s x A.domain ∧ J i x = y := by
  intro i x y
  refine ⟨fun h => ⟨coded_function_domain (A.iso i).1 h, hJ i x y h⟩, ?_⟩
  rintro ⟨hx, hxy⟩
  obtain ⟨z, hxz, _⟩ := (A.iso i).1.2 x hx
  exact ((hJ i x z hxz).symm.trans hxy) ▸ hxz

/-- The complete no-choice candidate construction can begin with any
    prescribed whole-group action retaining the Quine label action. -/
theorem countable_bafa_prescribed_covered_candidate (base : BaseCollection s) (hB : BAFACode s)
    {z w : U} (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (A : CodedMaskAction base w)
    (hlabel : ∀ i x, (∃ c, s c P.family ∧ s x c) →
      CodedRelation s (A.maps i) x (maskedLabelAction P i.val x))
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ i x y, CodedRelation s (A.maps i) x y → J i x = y) ∧
      CoveredCandidateLaws J ∧
      (∀ x, s x A.domain → (ActionCovered base A x ↔ InternalMaskCovered s w J x)) ∧
      (BaseCollection (coveredMaskMember J) ↔ CoveredTailFixedSourceBounds s w J) := by
  obtain ⟨J, hJ, hOne, hMul, hAJ, hCover, hBAFA⟩ :=
    countable_bafa_scheduled_mask_action base hB hw A enum henum
  have hj : ∀ i, ElementaryMap s s (J i) := fun i => (hJ i).1
  have ho := fun i => (hJ i).2.1
  have hl := fun i => (hJ i).2.2
  have hc : ∀ i j x, J i (J j x) = J j (J i x) := fun i j x =>
    group_action_preserves_commutation (internalMaskGroup base w) J hMul (internal_mask_mul_comm base i j) x
  have hs : ∀ i x, J i (J i x) = x := by
    intro i x
    have h := hMul i i x
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (hOne x)
  have hcore : ∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x :=
    fun i x hx => hAJ i x _ (hlabel i x hx)
  have hCover' : ∀ d, ∃ T, Nonempty (JointMaskDomain s w J T) ∧ Subset s d T := by
    intro d
    obtain ⟨T, _, hT, hd⟩ := hCover d
    exact ⟨T, hT, hd⟩
  have hp := covered_mask_pairing base hw J hj
  have hu := covered_mask_union base J hj ho
  have hpow := covered_mask_power base hj hc hs hCover'
  have hsep := covered_mask_bounded_separation base hw J hj ho
  have hlaws : CoveredCandidateLaws J :=
    ⟨covered_mask_extensional base.extensional J, covered_mask_empty base hw J hj ho,
      hp, hu, hpow, covered_mask_infinity base hw J hl, hsep,
      power_bounded_separation_of_bounded hp hu hpow hsep, covered_mask_bafa base hj hs hBAFA,
      covered_mask_not_choice base hw P hj ho hcore,
      covered_mask_transitive_containment base hw hj hc hs hCover⟩
  exact ⟨J, hJ, hAJ, hlaws,
    fun x hx => action_covered_iff_global base A (coded_action_global_agreement base A hAJ) hx,
    covered_base_iff_tail_fixed_source_bounds base hw hj hl hc hs hOne hMul hCover⟩

/-- One entire prescribed local action, not merely finitely many points,
    embeds into an actual scheduled candidate. The candidate may depend on Q;
    a single candidate realizing all compatible Q is not asserted here. -/
theorem countable_bafa_amalgamated_covered_candidate (base : BaseCollection s) (hB : BAFACode s)
    {z w t : U} (hw : OmegaCode s z w) (L : InternalQuinePairs s w)
    (P Q : CodedMaskAction base w)
    (hlabel : ∀ i x, (∃ c, s c L.family ∧ s x c) →
      CodedRelation s (P.maps i) x (maskedLabelAction L i.val x))
    (ht : TransitiveCode s t) (htP : Subset s t P.domain) (htQ : Subset s t Q.domain)
    (hstable : ∀ i x y, s x t → CodedRelation s (P.maps i) x y → s y t)
    (hag : ∀ i x y, s x t → (CodedRelation s (P.maps i) x y ↔ CodedRelation s (Q.maps i) x y))
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ C : CodedMaskAction base w, ∃ f, ∃ J : InternalMask s w → U → U,
      Subset s P.domain C.domain ∧ Nonempty (CodedMaskEmbedding base Q C f) ∧
      (∀ x, s x t → CodedRelation s f x x) ∧
      (∀ i x y, CodedRelation s (P.maps i) x y → J i x = y) ∧
      (∀ i x y, CodedRelation s (C.maps i) x y → J i x = y) ∧
      CoveredCandidateLaws J ∧
      (∀ x X, CodedRelation s f x X → (ActionCovered base Q x ↔ InternalMaskCovered s w J X)) ∧
      (BaseCollection (coveredMaskMember J) ↔ CoveredTailFixedSourceBounds s w J) := by
  obtain ⟨C, f, hPC, _, hOld, ⟨E⟩, hfix⟩ := bafa_coded_mask_amalgamation base hB P Q ht htP htQ hstable hag
  have hCLabel : ∀ i x, (∃ c, s c L.family ∧ s x c) →
      CodedRelation s (C.maps i) x (maskedLabelAction L i.val x) :=
    fun i x hx => hOld i x _ (hlabel i x hx)
  obtain ⟨J, _, hCJ, hlaws, hcov, hbase⟩ :=
    countable_bafa_prescribed_covered_candidate base hB hw L C hCLabel enum henum
  exact ⟨C, f, J, hPC, ⟨E⟩, hfix, fun i x y hxy => hCJ i x y (hOld i x y hxy), hCJ,
    hlaws, fun x X hxX => (coded_mask_embedding_cover_iff base E hxX).trans
      (hcov X (coded_mask_embedding_value base E hxX)), hbase⟩

#print axioms countable_bafa_amalgamated_covered_candidate
end FullBridge
