import LocalActionTruthInterfaces
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Full existential truth is witnessed by a compatible source action extension.
    The body is now an arbitrary finite formula, still interpreted semantically
    by LocalActionTruth; eliminating that semantic predicate from source syntax
    remains a separate task. -/
theorem local_action_truth_exists (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) {n} (p : Formula (n+1)) (v : Fin n → U)
    (hv : ∀ j, s (v j) A.domain) :
    LocalActionTruth base J (.ex p) A v ↔
      ∃ C : CodedMaskAction base w, CodedMaskExtends base A C ∧
        ∃ y, ActionCovered base C y ∧ LocalActionTruth base J p C (cons y v) := by
  constructor
  · rintro ⟨B, f, E, hBJ, V, hf, X, hp⟩
    obtain ⟨R, hRd, ⟨I⟩, hRJ⟩ := global_embedding_image_action base ctx.elementary ctx.involutive ctx.one ctx.mul E hBJ
    obtain ⟨k, ⟨Ik⟩, hk⟩ := coded_mask_isomorphism_inverse base I
    obtain ⟨Q, hBQ, hXQ, hQJ⟩ := global_coded_action_extend_point base ctx.elementary ctx.involutive ctx.one ctx.mul
      ctx.cover B hBJ X.val
    have hRB : Subset s R.domain B.domain := fun x hx => E.subset x (hRd ▸ hx)
    have hRQ : CodedMaskExtends base R Q := by
      refine ⟨fun x hx => hBQ.1 x (hRB x hx), ?_⟩
      intro i x y hxy
      exact hBQ.2 i x y ((coded_action_global_agreement base B hBJ i x y).mpr
        ⟨hRB x (coded_function_domain (R.iso i).1 hxy), hRJ i x y hxy⟩)
    obtain ⟨C, g, hAC, ⟨Eg⟩, hkg⟩ := bafa_coded_mask_embedding_extension base ctx.bafa R A Q
      (Ik.toEmbedding base) hRQ
    obtain ⟨y, hXy, _⟩ := Eg.iso.1.2 X.val hXQ
    have hXcov := (action_covered_iff_global base Q (coded_action_global_agreement base Q hQJ) hXQ).mpr X.property
    have hQparams : ∀ j, s (cons X V j).val Q.domain := by
      intro j
      refine Fin.cases hXQ (fun j => ?_) j
      exact hBQ.1 (V j).val (coded_mask_embedding_value base E (hf j))
    have hlocal := (global_action_local_truth_iff base ctx Q hQJ p (cons X V) hQparams).mpr hp
    have hgparams : ∀ j, CodedRelation s g (cons X V j).val (cons y v j) := by
      intro j
      refine Fin.cases hXy (fun j => ?_) j
      exact hkg (V j).val (v j) ((hk (v j) (V j).val).mpr (hf j))
    exact ⟨C, hAC, y, coded_mask_embedding_cover_forward base Eg hXy hXcov,
      (local_action_truth_embedding base ctx Eg p (fun j => (cons X V j).val) (cons y v) hgparams).mp hlocal⟩
  · rintro ⟨C, hAC, y, _, hp⟩
    exact (local_action_truth_extension base ctx hAC (.ex p) v hv).mpr (local_action_truth_exists_intro base hp)

#print axioms local_action_truth_exists
end FullBridge
