import GlobalActionImages
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Bundles properties already realized by the constructed universal action.
    It assumes no Separation or Collection axiom of the covered carrier. -/
structure UniversalActionContext (base : BaseCollection s) {w : U}
    (J : InternalMask s w → U → U) : Prop where
  bafa : BAFACode s
  elementary : ∀ i, ElementaryMap s s (J i)
  involutive : ∀ i x, J i (J i x) = x
  one : ∀ x, J (internalMaskOne base w) x = x
  mul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x)
  cover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T
  universal : UniversalMaskRealizations base J

theorem global_action_iso_covered_iff (base : BaseCollection s) {w f x X : U}
    {J : InternalMask s w → U → U} {A B : CodedMaskAction base w}
    (I : CodedMaskIsomorphism base A B f)
    (hAJ : ∀ i y Y, CodedRelation s (A.maps i) y Y → J i y = Y)
    (hBJ : ∀ i y Y, CodedRelation s (B.maps i) y Y → J i y = Y)
    (hx : CodedRelation s f x X) : InternalMaskCovered s w J x ↔ InternalMaskCovered s w J X := by
  have hxA := coded_function_domain I.iso.1 hx
  have hXB := (I.iso.2.2.1 X).mpr ⟨x, hxA, hx⟩
  exact (action_covered_iff_global base A (coded_action_global_agreement base A hAJ) hxA).symm.trans
    ((coded_mask_embedding_cover_iff base (I.toEmbedding base) hx).trans
      (action_covered_iff_global base B (coded_action_global_agreement base B hBJ) hXB))

/-- Extend any global-compatible partial isomorphism to include any source
    point. Inverse isomorphisms give the corresponding back step. -/
theorem universal_action_iso_forth (base : BaseCollection s) {w f : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    {A B : CodedMaskAction base w} (I : CodedMaskIsomorphism base A B f)
    (hAJ : ∀ i y Y, CodedRelation s (A.maps i) y Y → J i y = Y)
    (hBJ : ∀ i y Y, CodedRelation s (B.maps i) y Y → J i y = Y) (x : U) :
    ∃ A' B' : CodedMaskAction base w, ∃ g, CodedMaskExtends base A A' ∧ s x A'.domain ∧
      (∀ i y Y, CodedRelation s (A'.maps i) y Y → J i y = Y) ∧
      Nonempty (CodedMaskIsomorphism base A' B' g) ∧
      (∀ i y Y, CodedRelation s (B'.maps i) y Y → J i y = Y) ∧
      ∀ y Y, CodedRelation s f y Y → CodedRelation s g y Y := by
  obtain ⟨Q, hAQ, hxQ, hQJ⟩ := global_coded_action_extend_point base ctx.elementary ctx.involutive
    ctx.one ctx.mul ctx.cover A hAJ x
  obtain ⟨C, g, hBC, ⟨Eg⟩, hfg⟩ := bafa_coded_mask_embedding_extension base ctx.bafa A B Q (I.toEmbedding base) hAQ
  obtain ⟨D, k, ⟨Ek⟩, hDJ, hfix⟩ := ctx.universal B.domain C
    (coded_action_extension_global_compatible base B C hBJ hBC)
  obtain ⟨l, ⟨El⟩, hl⟩ := coded_mask_embeddings_compose base Eg Ek
  obtain ⟨B', _, ⟨Il⟩, hB'J⟩ := global_embedding_image_action base ctx.elementary ctx.involutive ctx.one ctx.mul El hDJ
  refine ⟨Q, B', l, hAQ, hxQ, hQJ, ⟨Il⟩, hB'J, ?_⟩
  intro y Y hyY
  exact (hl y Y).mpr ⟨Y, hfg y Y hyY,
    hfix Y ((I.iso.2.2.1 Y).mpr ⟨y, coded_function_domain I.iso.1 hyY, hyY⟩)⟩

#print axioms universal_action_iso_forth
end FullBridge
