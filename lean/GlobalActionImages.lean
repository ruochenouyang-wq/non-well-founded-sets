import CodedMaskIsomorphisms
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem coded_action_joint_domain (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (A : CodedMaskAction base w)
    (hAJ : ∀ i x y, CodedRelation s (A.maps i) x y → J i x = y) :
    Nonempty (JointMaskDomain s w J A.domain) := by
  refine ⟨⟨A.masks, A.maskMembers, A.family, A.familyFunction, ?_,
    coded_action_global_stable base A hAJ⟩⟩
  intro i f hif
  have hf := coded_function_value_unique A.familyFunction hif (A.mapCodes i)
  subst f
  exact ⟨(A.iso i).1, coded_action_global_agreement base A hAJ i⟩

/-- The image of an equivariant embedding into J carries its own actual
    jointly coded action, making the embedding onto that action domain. -/
theorem global_embedding_image_action (base : BaseCollection s) {w f : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hs : ∀ i x, J i (J i x) = x) (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    (hBJ : ∀ i x y, CodedRelation s (B.maps i) x y → J i x = y) :
    ∃ C : CodedMaskAction base w, C.domain = E.range ∧
      Nonempty (CodedMaskIsomorphism base A C f) ∧
      ∀ i x y, CodedRelation s (C.maps i) x y → J i x = y := by
  obtain ⟨K⟩ := coded_action_joint_domain base B hBJ
  have hstable : ∀ i X, s X E.range → s (J i X) E.range := by
    intro i X hX
    obtain ⟨x, hx, hxX⟩ := (E.iso.2.2.1 X).mp hX
    obtain ⟨y, hxy, _⟩ := (A.iso i).1.2 x hx
    have hy := ((A.iso i).2.2.1 y).mpr ⟨x, hx, hxy⟩
    obtain ⟨Y, hyY, _⟩ := E.iso.1.2 y hy
    have hJ := hBJ i X Y (E.intertwines i x y X Y hxy hxX hyY)
    exact hJ.symm ▸ (E.iso.2.2.1 Y).mpr ⟨y, hy, hyY⟩
  obtain ⟨L⟩ := joint_mask_domain_restrict base K E.subset hstable
  obtain ⟨C, hd, _, _, hC⟩ := joint_mask_coded_action base L E.transitive hj hs hOne hMul
  have hmem : MembershipIsoCode s A.domain C.domain f := hd.symm ▸ E.iso
  refine ⟨C, hd, ⟨⟨hmem, ?_⟩⟩, fun i x y h => ((hC i x y).mp h).2⟩
  intro i x y X Y hxy hxX hyY
  exact (hC i X Y).mpr ⟨(E.iso.2.2.1 X).mpr ⟨x, coded_function_domain E.iso.1 hxX, hxX⟩,
    hBJ i X Y (E.intertwines i x y X Y hxy hxX hyY)⟩

theorem global_coded_action_extend_point (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hs : ∀ i x, J i (J i x) = x) (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (A : CodedMaskAction base w) (hAJ : ∀ i x y, CodedRelation s (A.maps i) x y → J i x = y)
    (x : U) : ∃ Q : CodedMaskAction base w, CodedMaskExtends base A Q ∧ s x Q.domain ∧
      ∀ i y Y, CodedRelation s (Q.maps i) y Y → J i y = Y := by
  obtain ⟨d, hAd, hxd⟩ := power_finite_environment_bound base.pairing base.union A.domain (cons x Fin.elim0)
  obtain ⟨T, hT, ⟨K⟩, hdT⟩ := hCover d
  obtain ⟨Q, hd, _, _, hr⟩ := joint_mask_coded_action base K hT hj hs hOne hMul
  have hAQ : CodedMaskExtends base A Q := by
    refine ⟨fun y hy => hd.symm ▸ hdT y (hAd y hy), ?_⟩
    intro i y Y h
    exact (hr i y Y).mpr ⟨hdT y (hAd y (coded_function_domain (A.iso i).1 h)), hAJ i y Y h⟩
  exact ⟨Q, hAQ, hd.symm ▸ hdT x (hxd 0), fun i y Y h => ((hr i y Y).mp h).2⟩

#print axioms global_embedding_image_action
end FullBridge
