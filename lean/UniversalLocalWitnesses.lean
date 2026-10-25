import UniversalCoveredCandidate
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem coded_action_global_stable (base : BaseCollection s) {w : U} (A : CodedMaskAction base w)
    {J : InternalMask s w → U → U} (hAJ : ∀ i x y, CodedRelation s (A.maps i) x y → J i x = y) :
    ∀ i x, s x A.domain → s (J i x) A.domain := by
  intro i x hx
  obtain ⟨y, hxy, _⟩ := (A.iso i).1.2 x hx
  exact (hAJ i x y hxy).symm ▸ ((A.iso i).2.2.1 y).mpr ⟨x, hx, hxy⟩

theorem coded_action_extension_global_compatible (base : BaseCollection s) {w : U}
    (A Q : CodedMaskAction base w) {J : InternalMask s w → U → U}
    (hAJ : ∀ i x y, CodedRelation s (A.maps i) x y → J i x = y)
    (hAQ : CodedMaskExtends base A Q) : GlobalActionCompatible base J A.domain Q := by
  refine ⟨A.transitive, hAQ.1, coded_action_global_stable base A hAJ, ?_⟩
  intro i x y hx
  constructor
  · intro hxy
    obtain ⟨z, hxz, _⟩ := (A.iso i).1.2 x hx
    exact (hAJ i x z hxz).trans (coded_function_value_unique (Q.iso i).1 (hAQ.2 i x z hxz) hxy)
  · intro hxy
    exact hAQ.2 i x y ((coded_action_global_agreement base A hAJ i x y).mpr ⟨hx, hxy⟩)

/-- Existential bounded truth in the one universal Hc is exactly witnessed
    by a compatible local action extension with a covered source witness.
    Quantification over action records has not yet been translated into a
    single first-order source formula. -/
theorem universal_Hc_bounded_existential_certificate (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hs : ∀ i x, J i (J i x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (hUniversal : UniversalMaskRealizations base J)
    (A : CodedMaskAction base w)
    (hAJ : ∀ i x y, CodedRelation s (A.maps i) x y → J i x = y)
    {n} (p : BoundedFormula (n+1)) (v : Fin n → CoveredMaskCarrier s w J)
    (hv : ∀ j, s (v j).val A.domain) :
    (∃ y, BoundedEval (coveredMaskMember J) p (cons y v)) ↔
      ∃ Q : CodedMaskAction base w, CodedMaskExtends base A Q ∧
        ∃ y, ActionCovered base Q y ∧ BoundedEval s p (cons y (fun j => (v j).val)) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨d, hAd, hyd⟩ := power_finite_environment_bound base.pairing base.union A.domain (cons y.val Fin.elim0)
    obtain ⟨T, hT, ⟨K⟩, hdT⟩ := hCover d
    obtain ⟨Q, hQd, _, _, hQr⟩ := joint_mask_coded_action base K hT hj hs hOne hMul
    have hAQ : CodedMaskExtends base A Q := by
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [hQd]
        exact hdT x (hAd x hx)
      · intro i x X hxX
        exact (hQr i x X).mpr ⟨hdT x (hAd x (coded_function_domain (A.iso i).1 hxX)), hAJ i x X hxX⟩
    have hyQ : s y.val Q.domain := by
      rw [hQd]
      exact hdT y.val (hyd 0)
    have hQJ : ∀ i x X, CodedRelation s (Q.maps i) x X → J i x = X :=
      fun i x X hxX => ((hQr i x X).mp hxX).2
    have hycov := (action_covered_iff_global base Q (coded_action_global_agreement base Q hQJ) hyQ).mpr y.property
    have hyp := (covered_mask_bounded_absoluteness p (cons y v)).mp hy
    rw [covered_mask_cons_values] at hyp
    exact ⟨Q, hAQ, y.val, hycov, hyp⟩
  · rintro ⟨Q, hAQ, y, hycov, hyp⟩
    obtain ⟨C, f, ⟨E⟩, hCJ, hfix⟩ := hUniversal A.domain Q
      (coded_action_extension_global_compatible base A Q hAJ hAQ)
    have hyQ : s y Q.domain := by
      obtain ⟨c, hcQ, _, hyc, _⟩ := hycov
      exact hcQ y hyc
    obtain ⟨Y, hyY, _⟩ := E.iso.1.2 y hyQ
    obtain ⟨YY, _, hsem⟩ := coded_action_bounded_witness_into_Hc base E hCJ p v
      (fun j => hfix (v j).val (hv j)) hyY hycov
    exact ⟨YY, hsem.mp hyp⟩

#print axioms universal_Hc_bounded_existential_certificate
end FullBridge
