import UniversalActionSemantics
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem universal_any_action_realized (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) :
    ∃ B : CodedMaskAction base w, ∃ f, Nonempty (CodedMaskEmbedding base A B f) ∧
      ∀ i x y, CodedRelation s (B.maps i) x y → J i x = y := by
  obtain ⟨e, he⟩ := base.empty
  have hc : GlobalActionCompatible base J e A :=
    ⟨fun x hx => False.elim (he x hx), fun x hx => False.elim (he x hx),
      fun i x hx => False.elim (he x hx), fun i x y hx => False.elim (he x hx)⟩
  obtain ⟨B, f, hE, hBJ, _⟩ := ctx.universal e A hc
  exact ⟨B, f, hE, hBJ⟩

/-- Two realizations of the same local action give the same full Hc truth
    for corresponding covered parameters. Neither realization is privileged. -/
theorem local_realizations_full_semantics (base : BaseCollection s) {w f g : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    {A B C : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    (F : CodedMaskEmbedding base A C g)
    (hBJ : ∀ i x y, CodedRelation s (B.maps i) x y → J i x = y)
    (hCJ : ∀ i x y, CodedRelation s (C.maps i) x y → J i x = y)
    {n} (p : Formula n) (v : Fin n → U) (V W : Fin n → CoveredMaskCarrier s w J)
    (hv : ∀ j, CodedRelation s f (v j) (V j).val)
    (hw : ∀ j, CodedRelation s g (v j) (W j).val) :
    Eval (coveredMaskMember J) p V ↔ Eval (coveredMaskMember J) p W := by
  obtain ⟨B', _, ⟨If⟩, hb⟩ := global_embedding_image_action base ctx.elementary ctx.involutive ctx.one ctx.mul E hBJ
  obtain ⟨C', _, ⟨Ig⟩, hc⟩ := global_embedding_image_action base ctx.elementary ctx.involutive ctx.one ctx.mul F hCJ
  obtain ⟨k, ⟨Ik⟩, hk⟩ := coded_mask_isomorphism_inverse base If
  obtain ⟨l, ⟨Il⟩, hl⟩ := coded_mask_isomorphisms_compose base Ik Ig
  exact universal_action_iso_semantics base ctx p Il hb hc V W
    (fun j => (hl (V j).val (W j).val).mpr ⟨v j, (hk (v j) (V j).val).mpr (hv j), hw j⟩)

/-- Semantic local truth via a realization into the single Hc. This definition
    still mentions J and Hc and is not itself a first-order source formula. -/
def LocalActionTruth (base : BaseCollection s) {w : U} (J : InternalMask s w → U → U)
    {n} (p : Formula n) (A : CodedMaskAction base w) (v : Fin n → U) : Prop :=
  ∃ B : CodedMaskAction base w, ∃ f, ∃ _E : CodedMaskEmbedding base A B f,
    (∀ i x y, CodedRelation s (B.maps i) x y → J i x = y) ∧
    ∃ V : Fin n → CoveredMaskCarrier s w J,
      (∀ j, CodedRelation s f (v j) (V j).val) ∧ Eval (coveredMaskMember J) p V

theorem local_action_truth_realization_iff (base : BaseCollection s) {w f : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    (hBJ : ∀ i x y, CodedRelation s (B.maps i) x y → J i x = y)
    {n} (p : Formula n) (v : Fin n → U) (V : Fin n → CoveredMaskCarrier s w J)
    (hv : ∀ j, CodedRelation s f (v j) (V j).val) :
    LocalActionTruth base J p A v ↔ Eval (coveredMaskMember J) p V := by
  constructor
  · rintro ⟨C, g, F, hc, W, hw, hp⟩
    exact (local_realizations_full_semantics base ctx F E hc hBJ p v W V hw hv).mp hp
  · exact fun hp => ⟨B, f, E, hBJ, V, hv, hp⟩

theorem local_action_truth_parameters_covered (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} {n} {p : Formula n}
    {A : CodedMaskAction base w} {v : Fin n → U} (h : LocalActionTruth base J p A v) :
    ∀ j, s (v j) A.domain ∧ ActionCovered base A (v j) := by
  obtain ⟨B, f, E, hBJ, V, hv, _⟩ := h
  intro j
  have hj := hv j
  have hV := (action_covered_iff_global base B (coded_action_global_agreement base B hBJ)
    (coded_mask_embedding_value base E hj)).mpr (V j).property
  exact ⟨coded_function_domain E.iso.1 hj, coded_mask_embedding_cover_reflects base E hj hV⟩

/-- Full local truth is transported through any actual equivariant embedding,
    even when its source and target actions are not literal restrictions of J. -/
theorem local_action_truth_embedding (base : BaseCollection s) {w f : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    {n} (p : Formula n) (v V : Fin n → U)
    (hv : ∀ j, CodedRelation s f (v j) (V j)) :
    LocalActionTruth base J p A v ↔ LocalActionTruth base J p B V := by
  constructor
  · intro hp
    classical
    have hc := local_action_truth_parameters_covered base hp
    obtain ⟨C, g, ⟨F⟩, hCJ⟩ := universal_any_action_realized base ctx B
    have hw : ∀ j, ∃ Y : CoveredMaskCarrier s w J, CodedRelation s g (V j) Y.val := by
      intro j
      obtain ⟨Y, hY, _⟩ := F.iso.1.2 (V j) (coded_mask_embedding_value base E (hv j))
      have hcov := coded_mask_embedding_cover_forward base F hY
        (coded_mask_embedding_cover_forward base E (hv j) (hc j).2)
      have hglobal := (action_covered_iff_global base C (coded_action_global_agreement base C hCJ)
        (coded_mask_embedding_value base F hY)).mp hcov
      exact ⟨⟨Y, hglobal⟩, hY⟩
    let W : Fin n → CoveredMaskCarrier s w J := fun j => Classical.choose (hw j)
    have hW : ∀ j, CodedRelation s g (V j) (W j).val := fun j => Classical.choose_spec (hw j)
    obtain ⟨k, ⟨K⟩, hk⟩ := coded_mask_embeddings_compose base E F
    have hkv := fun j => (hk (v j) (W j).val).mpr ⟨V j, hv j, hW j⟩
    exact (local_action_truth_realization_iff base ctx F hCJ p V W hW).mpr
      ((local_action_truth_realization_iff base ctx K hCJ p v W hkv).mp hp)
  · rintro ⟨C, g, F, hCJ, W, hW, hp⟩
    obtain ⟨k, ⟨K⟩, hk⟩ := coded_mask_embeddings_compose base E F
    exact ⟨C, k, K, hCJ, W, fun j => (hk (v j) (W j).val).mpr ⟨V j, hv j, hW j⟩, hp⟩

#print axioms local_action_truth_embedding
end FullBridge
