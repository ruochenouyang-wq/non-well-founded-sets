import FullWitnessFamilies
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Full-formula witness images, not merely source codes, have one source bound. -/
theorem universal_Hc_full_source_bound (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) (hAJ : ∀ i x y, CodedRelation s (A.maps i) x y → J i x = y)
    {n} (p : Formula (n+2)) (v : Fin n → CoveredMaskCarrier s w J) (a : CoveredMaskCarrier s w J)
    (ha : Subset s a.val A.domain) (hv : ∀ j, s (v j).val A.domain)
    (ht : ∀ x, coveredMaskMember J x a → ∃ y, Eval (coveredMaskMember J) p (cons y (cons x v))) :
    ∃ b, ∀ x, coveredMaskMember J x a → ∃ y : CoveredMaskCarrier s w J,
      s y.val b ∧ Eval (coveredMaskMember J) p (cons y (cons x v)) := by
  have hac : ∀ x, s x a.val → ActionCovered base A x := fun x hx =>
    (action_covered_iff_global base A (coded_action_global_agreement base A hAJ) (ha x hx)).mpr
      (internal_mask_covered_member a.property hx)
  have hvc : ∀ j, ActionCovered base A (v j).val := fun j =>
    (action_covered_iff_global base A (coded_action_global_agreement base A hAJ) (hv j)).mpr (v j).property
  have hl : ∀ x, s x a.val → ∃ Q : CodedMaskAction base w, CodedMaskExtends base A Q ∧
      ∃ y, ActionCovered base Q y ∧ LocalActionTruth base J p Q (cons y (cons x (fun j => (v j).val))) := by
    intro x hx
    let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member a.property hx⟩
    have hp := (global_action_local_truth_iff base ctx A hAJ (.ex p) (cons X v)
      (fun j => Fin.cases (ha x hx) (fun j => hv j) j)).mpr (ht X hx)
    rw [covered_mask_cons_values] at hp
    exact (local_action_truth_exists base ctx A p (cons x (fun j => (v j).val))
      (fun j => Fin.cases (ha x hx) (fun j => hv j) j)).mp hp
  obtain ⟨C, hAC, hC⟩ := full_witness_common_action base ctx A p (fun j => (v j).val) a.val hac hvc hl
  obtain ⟨D, g, ⟨E⟩, hDJ, hfix⟩ := ctx.universal A.domain C
    (coded_action_extension_global_compatible base A C hAJ hAC)
  refine ⟨D.domain, fun x hx => ?_⟩
  obtain ⟨y, hy, hp⟩ := hC x.val hx
  obtain ⟨Y, hyY, _⟩ := E.iso.1.2 y (action_covered_domain base hy)
  have hYcov := (action_covered_iff_global base D (coded_action_global_agreement base D hDJ)
    (coded_mask_embedding_value base E hyY)).mp (coded_mask_embedding_cover_forward base E hyY hy)
  let YY : CoveredMaskCarrier s w J := ⟨Y, hYcov⟩
  have hparams : ∀ j, CodedRelation s g (cons y (cons x.val (fun j => (v j).val)) j)
      (cons YY (cons x v) j).val := fun j => Fin.cases hyY
        (fun j => Fin.cases (hfix x.val (ha x.val hx)) (fun j => hfix (v j).val (hv j)) j) j
  exact ⟨YY, coded_mask_embedding_value base E hyY,
    (local_action_truth_realization_iff base ctx E hDJ p _ (cons YY (cons x v)) hparams).mp hp⟩

/-- The full actual first-order Collection scheme holds in the single Hc. -/
theorem universal_Hc_full_collection (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (ctx : UniversalActionContext base J) : Collection (coveredMaskMember J) := by
  intro n p v a ht
  obtain ⟨d, had, hvd⟩ := power_finite_environment_bound base.pairing base.union a.val (fun j => (v j).val)
  obtain ⟨T, hT, ⟨K⟩, hdT⟩ := ctx.cover d
  obtain ⟨A, hAd, _, _, hAr⟩ := joint_mask_coded_action base K hT ctx.elementary ctx.involutive ctx.one ctx.mul
  have ha : Subset s a.val A.domain := fun x hx => hAd.symm ▸ hdT x (had x hx)
  have hv : ∀ j, s (v j).val A.domain := fun j => hAd.symm ▸ hdT (v j).val (hvd j)
  obtain ⟨b, hb⟩ := universal_Hc_full_source_bound base ctx
    A (fun i x y h => ((hAr i x y).mp h).2) p v a ha hv ht
  have hcomm : ∀ i j x, J i (J j x) = J j (J i x) := by
    intro i j x
    rw [← ctx.mul, internal_mask_mul_comm base i j, ctx.mul]
  obtain ⟨B, _, hbound⟩ := covered_mask_absorbs_source_bound base hw ctx.elementary hcomm ctx.involutive ctx.cover b
  refine ⟨B, fun x hx => ?_⟩
  obtain ⟨y, hy, hp⟩ := hb x hx
  exact ⟨y, hbound y hy, hp⟩

#print axioms universal_Hc_full_collection
end FullBridge
