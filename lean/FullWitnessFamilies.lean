import FullWitnessPackages
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Source Collection is applied to the actual full-translation package
    formula, not to the semantic predicate in this theorem statement. -/
theorem full_witness_action_family (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) {n} (p : Formula (n+2)) (v : Fin n → U) (a : U)
    (ha : ∀ x, s x a → ActionCovered base A x) (hv : ∀ j, ActionCovered base A (v j))
    (ht : ∀ x, s x a → ∃ Q : CodedMaskAction base w, CodedMaskExtends base A Q ∧
      ∃ y, ActionCovered base Q y ∧ LocalActionTruth base J p Q (cons y (cons x v))) :
    ∃ O, ActionFamilyCode base w O ∧
      (∀ P Q, s P O → ActionFamilyMember base P Q → CodedMaskExtends base A Q) ∧
      ∀ x, s x a → ∃ P, s P O ∧ ∃ Q : CodedMaskAction base w, ∃ y,
        OrbitGraphParameters s P y Q.domain Q.family ∧ CodedMaskExtends base A Q ∧
          ActionCovered base Q y ∧ LocalActionTruth base J p Q (cons y (cons x v)) := by
  obtain ⟨B, hB⟩ := base.collection (n+4) (fullWitnessPackageFormula p)
    (cons w (cons A.domain (cons A.masks (cons A.family v)))) a (by
      intro x hx
      obtain ⟨Q, he, y, hc, hp⟩ := ht x hx
      obtain ⟨P, hP⟩ := orbit_graph_parameters_exists base y Q.domain Q.family
      exact ⟨P, (full_witness_package_iff_record base ctx A p P x v (ha x hx) hv).mpr ⟨Q, y, hP, he, hc, hp⟩⟩)
  obtain ⟨O, hO⟩ := base.separation (n+5) (fullWitnessFamilyFilterFormula p)
    (cons w (cons A.domain (cons A.masks (cons A.family (cons a v))))) B
  have hm : ∀ P, s P O ↔ s P B ∧ ∃ x, s x a ∧ Eval s (fullWitnessPackageFormula p)
      (cons P (cons x (cons w (cons A.domain (cons A.masks (cons A.family v)))))) := by
    intro P
    exact (hO P).trans (and_congr Iff.rfl (eval_fullWitnessFamilyFilterFormula p P w A.domain A.masks A.family a v))
  refine ⟨O, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨_, x, hx, hh⟩ := (hm P).mp hP
    obtain ⟨Q, y, hy, _⟩ := (full_witness_package_iff_record base ctx A p P x v (ha x hx) hv).mp hh
    exact ⟨Q, y, hy⟩
  · intro P Q hP hQ
    obtain ⟨_, x, hx, hh⟩ := (hm P).mp hP
    obtain ⟨R, y, hy, he, _⟩ := (full_witness_package_iff_record base ctx A p P x v (ha x hx) hv).mp hh
    exact (action_family_member_unique base ⟨y, hy⟩ hQ) ▸ he
  · intro x hx
    obtain ⟨P, hPB, hp⟩ := hB x hx
    exact ⟨P, (hm P).mpr ⟨hPB, x, hx, hp⟩,
      (full_witness_package_iff_record base ctx A p P x v (ha x hx) hv).mp hp⟩

/-- All arbitrary-formula witnesses can be put in one source action while
    preserving their full local truth and the input parameters. -/
theorem full_witness_common_action (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) {n} (p : Formula (n+2)) (v : Fin n → U) (a : U)
    (ha : ∀ x, s x a → ActionCovered base A x) (hv : ∀ j, ActionCovered base A (v j))
    (ht : ∀ x, s x a → ∃ Q : CodedMaskAction base w, CodedMaskExtends base A Q ∧
      ∃ y, ActionCovered base Q y ∧ LocalActionTruth base J p Q (cons y (cons x v))) :
    ∃ C : CodedMaskAction base w, CodedMaskExtends base A C ∧
      ∀ x, s x a → ∃ y, ActionCovered base C y ∧ LocalActionTruth base J p C (cons y (cons x v)) := by
  obtain ⟨O, hO, he, hw⟩ := full_witness_action_family base ctx A p v a ha hv ht
  obtain ⟨C, hAC, hC⟩ := bafa_coded_mask_family_amalgamation base ctx.bafa A hO he
  refine ⟨C, hAC, fun x hx => ?_⟩
  obtain ⟨P, hP, Q, y, hpar, _, hy, hp⟩ := hw x hx
  obtain ⟨f, ⟨E⟩, hfix⟩ := hC P Q hP ⟨y, hpar⟩
  obtain ⟨Y, hyY, _⟩ := E.iso.1.2 y (action_covered_domain base hy)
  have hparams : ∀ j, CodedRelation s f (cons y (cons x v) j) (cons Y (cons x v) j) :=
    fun j => Fin.cases hyY (fun j => Fin.cases (hfix x (action_covered_domain base (ha x hx)))
      (fun j => hfix (v j) (action_covered_domain base (hv j))) j) j
  exact ⟨Y, coded_mask_embedding_cover_forward base E hyY hy,
    (local_action_truth_embedding base ctx E p _ _ hparams).mp hp⟩

#print axioms full_witness_common_action
end FullBridge
