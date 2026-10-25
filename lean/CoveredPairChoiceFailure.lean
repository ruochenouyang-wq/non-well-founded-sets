import AfaPairChoiceBoundary
import CompleteChoiceSeparation

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem covered_quine_pair_members {w : U} (P : InternalQuinePairs s w)
    {J : InternalMask s w → U → U} (c : CoveredMaskCarrier s w J)
    (hc : s c.val P.family) : TwoElement (coveredMaskMember J) c ∧
      (∀ v, coveredMaskMember J v c → SelfSingleton (coveredMaskMember J) v) := by
  obtain ⟨i, l, r, _, hl, hr, hp⟩ := (P.members c.val).mp hc
  have hlc := (hp l).mpr (Or.inl rfl)
  have hrc := (hp r).mpr (Or.inr rfl)
  let L : CoveredMaskCarrier s w J := ⟨l, internal_mask_covered_member c.property hlc⟩
  let R : CoveredMaskCarrier s w J := ⟨r, internal_mask_covered_member c.property hrc⟩
  have hne : L ≠ R := fun h => internal_quine_pair_distinct P hl hr (congrArg Subtype.val h)
  refine ⟨⟨L, R, hne, ?_⟩, ?_⟩
  · intro v
    constructor
    · intro hv
      rcases (hp v.val).mp hv with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · intro hv
      rcases hv with rfl | rfl
      · exact hlc
      · exact hrc
  · intro v hv t
    have hq : SelfSingleton s v.val := by
      rcases (hp v.val).mp hv with h | h
      · exact h ▸ P.leftQuine i l hl
      · exact h ▸ P.rightQuine i r hr
    exact (hq t.val).trans ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩

/-- The ambient label maps are not supplied as functions in the covered
    model. The pair family itself and both members of each row are covered. -/
theorem covered_mask_not_quine_pair_choice (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w)
    {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (ho : ∀ i y, ∃ x, J i x = y)
    (hcore : ∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) :
    ¬ QuinePairChoiceCode (coveredMaskMember J) := by
  intro hQC
  have hF := hereditary_mask_family base hw P J hj ho hcore
  let F : CoveredMaskCarrier s w J := ⟨P.family, quine_pair_family_internally_covered base P hF⟩
  obtain ⟨f, hf⟩ := hQC F (fun c hc => covered_quine_pair_members P c hc)
  exact global_selector_not_mask_supported base hw P J hj ho hcore
    (covered_mask_choice_function_ambient F f hf)
    (hereditary_mask_root (internal_mask_covered_hereditary f.property))

theorem countable_bafa_full_no_pair_choice_model (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ J : InternalMask s w → U → U,
      UniversalActionContext base J ∧ BaseCollection (coveredMaskMember J) ∧
      BAFACode (coveredMaskMember J) ∧ ¬ PairChoiceCode (coveredMaskMember J) ∧
      ¬ FiberPairChoiceCode (coveredMaskMember J) ∧ ¬ QuinePairChoiceCode (coveredMaskMember J) := by
  obtain ⟨z, w, hw, P, J, hJ, hOne, hMul, hcore, hCover, laws, hUniversal, _⟩ :=
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
  have hqc := covered_mask_not_quine_pair_choice base hw P
    (fun i => (hJ i).1) (fun i => (hJ i).2.1) hcore
  have hfc : ¬ FiberPairChoiceCode (coveredMaskMember J) :=
    fun h => hqc (fiber_pair_choice_implies_quine_pair_choice hbase h)
  have hpc : ¬ PairChoiceCode (coveredMaskMember J) :=
    fun h => hfc (pair_choice_implies_fiber_pair_choice h)
  exact ⟨z, w, hw, J, ctx, hbase, hbafa, hpc, hfc, hqc⟩

theorem countable_bafa_pair_choice_complete_bridge (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ M : BafaModel.{u}, ¬ PairChoiceCode M.mem ∧ ¬ FiberPairChoiceCode M.mem ∧
      ¬ QuinePairChoiceCode M.mem ∧ Replacement M.mem ∧
      BaseCollection M.behaviorQuotient.mem ∧ AFACode M.behaviorQuotient.mem ∧
      FiberPairChoiceCode M.behaviorQuotient.mem ∧ QuinePairChoiceCode M.behaviorQuotient.mem := by
  obtain ⟨z, w, _, J, _, hbase, hbafa, hpc, hfc, hqc⟩ :=
    countable_bafa_full_no_pair_choice_model base hB enum henum
  let M : BafaModel.{u} := ⟨CoveredMaskCarrier s w J, coveredMaskMember J, hbase, hbafa⟩
  exact ⟨M, hpc, hfc, hqc, collection_separation_replacement _ hbase.collection hbase.separation,
    M.behaviorQuotient.base, M.behaviorQuotient.antiFoundation,
    afa_fiber_pair_choice M.behaviorQuotient.base M.behaviorQuotient.antiFoundation,
    afa_quine_pair_choice M.behaviorQuotient.base M.behaviorQuotient.antiFoundation⟩

theorem countable_bafa_pair_choice_separation (base : BaseCollection s) (hB : BAFACode s)
    (hAC : ChoiceCode s) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ M : BafaModel.{u}, ¬ PairChoiceCode M.mem ∧ ¬ FiberPairChoiceCode M.mem ∧
      ¬ QuinePairChoiceCode M.mem ∧ ChoiceCode M.behaviorQuotient.mem ∧
      PairChoiceCode M.behaviorQuotient.mem := by
  obtain ⟨z, w, hw, J, ctx, hbase, hbafa, hpc, hfc, hqc⟩ :=
    countable_bafa_full_no_pair_choice_model base hB enum henum
  let M : BafaModel.{u} := ⟨CoveredMaskCarrier s w J, coveredMaskMember J, hbase, hbafa⟩
  have htarget : ChoiceCode M.behaviorQuotient.mem :=
    covered_quotient_inherits_ambient_choice base hw ctx hbase hAC
  exact ⟨M, hpc, hfc, hqc, htarget, choice_implies_pair_choice htarget⟩

end FullBridge
