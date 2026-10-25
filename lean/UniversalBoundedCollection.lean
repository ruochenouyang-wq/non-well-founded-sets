import LocalWitnessAmalgamation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- After one common amalgamation and one universal realization, all bounded
    witnesses have a common source bound on their actual Hc images. -/
theorem universal_Hc_bounded_source_bound (base : BaseCollection s) (hB : BAFACode s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hs : ∀ i x, J i (J i x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (hUniversal : UniversalMaskRealizations base J)
    (A : CodedMaskAction base w) (hAJ : ∀ i x y, CodedRelation s (A.maps i) x y → J i x = y)
    {n} (p : BoundedFormula (n+2)) (v : Fin n → CoveredMaskCarrier s w J) (a : CoveredMaskCarrier s w J)
    (ha : Subset s a.val A.domain) (hv : ∀ j, s (v j).val A.domain)
    (ht : ∀ x, coveredMaskMember J x a → ∃ y, BoundedEval (coveredMaskMember J) p (cons y (cons x v))) :
    ∃ b, ∀ x, coveredMaskMember J x a → ∃ y : CoveredMaskCarrier s w J,
      s y.val b ∧ BoundedEval (coveredMaskMember J) p (cons y (cons x v)) := by
  have hl : ∀ x, s x a.val → ∃ Q : CodedMaskAction base w, CodedMaskExtends base A Q ∧
      ∃ y, ActionCovered base Q y ∧ BoundedEval s p (cons y (cons x (fun j => (v j).val))) := by
    intro x hx
    let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member a.property hx⟩
    simpa only [covered_mask_cons_values] using (universal_Hc_bounded_existential_certificate base hj hs hOne hMul hCover hUniversal A hAJ
      p (cons X v) (fun j => Fin.cases (ha x hx) (fun j => hv j) j)).mp (ht X hx)
  obtain ⟨C, hAC, hC⟩ := local_witness_common_action base hB A p (fun j => (v j).val) a.val ha hv hl
  obtain ⟨D, g, ⟨E⟩, hDJ, hfix⟩ := hUniversal A.domain C
    (coded_action_extension_global_compatible base A C hAJ hAC)
  refine ⟨D.domain, fun x hx => ?_⟩
  obtain ⟨y, hy, hp⟩ := hC x.val hx
  have hyC : s y C.domain := by
    obtain ⟨c, hc, _, hyc, _⟩ := hy
    exact hc y hyc
  obtain ⟨Y, hyY, _⟩ := E.iso.1.2 y hyC
  obtain ⟨YY, hYY, hsem⟩ := coded_action_bounded_witness_into_Hc base E hDJ p (cons x v)
    (fun j => Fin.cases (hfix x.val (ha x.val hx)) (fun j => hfix (v j).val (hv j)) j) hyY hy
  rw [covered_mask_cons_values] at hsem
  exact ⟨YY, hYY.symm ▸ coded_mask_embedding_value base E hyY, hsem.mp hp⟩

/-- Collection for bounded formulas in Hc. Full Collection for arbitrary
    unbounded formulas remains a separate, unproved obligation. -/
theorem universal_Hc_bounded_collection (base : BaseCollection s) (hB : BAFACode s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hs : ∀ i x, J i (J i x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (hUniversal : UniversalMaskRealizations base J) :
    ∀ n (p : BoundedFormula (n+2)) (v : Fin n → CoveredMaskCarrier s w J) (a : CoveredMaskCarrier s w J),
      (∀ x, coveredMaskMember J x a → ∃ y, BoundedEval (coveredMaskMember J) p (cons y (cons x v))) →
      ∃ b, ∀ x, coveredMaskMember J x a → ∃ y,
        coveredMaskMember J y b ∧ BoundedEval (coveredMaskMember J) p (cons y (cons x v)) := by
  intro n p v a ht
  obtain ⟨d, had, hvd⟩ := power_finite_environment_bound base.pairing base.union a.val (fun j => (v j).val)
  obtain ⟨T, hT, ⟨K⟩, hdT⟩ := hCover d
  obtain ⟨A, hAd, _, _, hAr⟩ := joint_mask_coded_action base K hT hj hs hOne hMul
  have ha : Subset s a.val A.domain := fun x hx => hAd.symm ▸ hdT x (had x hx)
  have hv : ∀ j, s (v j).val A.domain := fun j => hAd.symm ▸ hdT (v j).val (hvd j)
  obtain ⟨b, hb⟩ := universal_Hc_bounded_source_bound base hB hj hs hOne hMul hCover hUniversal
    A (fun i x y h => ((hAr i x y).mp h).2) p v a ha hv ht
  have hcomm : ∀ i j x, J i (J j x) = J j (J i x) := by
    intro i j x
    rw [← hMul, internal_mask_mul_comm base i j, hMul]
  obtain ⟨B, _, hbound⟩ := covered_mask_absorbs_source_bound base hw hj hcomm hs hCover b
  refine ⟨B, fun x hx => ?_⟩
  obtain ⟨y, hy, hp⟩ := hb x hx
  exact ⟨y, hbound y hy, hp⟩

#print axioms universal_Hc_bounded_collection
end FullBridge
