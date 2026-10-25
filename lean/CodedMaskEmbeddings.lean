import ScheduledFixedInputReduction
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A source-coded membership isomorphism onto a transitive invariant range,
    intertwining every actual internal mask. No elementarity is assumed. -/
structure CodedMaskEmbedding (base : BaseCollection s) {w : U}
    (A B : CodedMaskAction base w) (f : U) where
  range : U
  transitive : TransitiveCode s range
  subset : Subset s range B.domain
  iso : MembershipIsoCode s A.domain range f
  intertwines : ∀ i x y X Y, CodedRelation s (A.maps i) x y →
    CodedRelation s f x X → CodedRelation s f y Y → CodedRelation s (B.maps i) X Y

theorem coded_mask_embedding_value (base : BaseCollection s) {w f x X : U}
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    (hx : CodedRelation s f x X) : s X B.domain :=
  E.subset X ((E.iso.2.2.1 X).mpr ⟨x, coded_function_domain E.iso.1 hx, hx⟩)

theorem coded_mask_embedding_action_iff (base : BaseCollection s) {w f x y X Y : U}
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    (i : InternalMask s w) (hx : CodedRelation s f x X) (hy : CodedRelation s f y Y) :
    CodedRelation s (A.maps i) x y ↔ CodedRelation s (B.maps i) X Y := by
  refine ⟨fun h => E.intertwines i x y X Y h hx hy, ?_⟩
  intro hXY
  obtain ⟨z, hxz, _⟩ := (A.iso i).1.2 x (coded_function_domain E.iso.1 hx)
  have hz := ((A.iso i).2.2.1 z).mpr ⟨x, coded_function_domain E.iso.1 hx, hxz⟩
  obtain ⟨Z, hzZ, _⟩ := E.iso.1.2 z hz
  have hXZ := E.intertwines i x z X Z hxz hx hzZ
  have hZY := coded_function_value_unique (B.iso i).1 hXZ hXY
  have hzy := E.iso.2.1 z y Y (hZY ▸ hzZ) hy
  exact hzy ▸ hxz

theorem coded_mask_embedding_behavior (base : BaseCollection s) {w f : U}
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f) :
    ∀ x X, CodedRelation s f x X → internalCode base x = internalCode base X :=
  fun x X hx => ((membership_iso_over_quotient base A.transitive E.transitive E.iso).2 x X hx).2

/-- Two prescribed joint actions can be amalgamated over an invariant
    transitive common part. P remains literal; Q is embedded injectively.
    No disjointness of the two resulting ranges is claimed. -/
theorem bafa_coded_mask_amalgamation (base : BaseCollection s) (hB : BAFACode s)
    {w t : U} (P Q : CodedMaskAction base w) (ht : TransitiveCode s t)
    (htP : Subset s t P.domain) (htQ : Subset s t Q.domain)
    (hstable : ∀ i x y, s x t → CodedRelation s (P.maps i) x y → s y t)
    (hag : ∀ i x y, s x t → (CodedRelation s (P.maps i) x y ↔ CodedRelation s (Q.maps i) x y)) :
    ∃ C : CodedMaskAction base w, ∃ f,
      Subset s P.domain C.domain ∧ C.masks = P.masks ∧
      (∀ i x y, CodedRelation s (P.maps i) x y → CodedRelation s (C.maps i) x y) ∧
      Nonempty (CodedMaskEmbedding base Q C f) ∧ (∀ x, s x t → CodedRelation s f x x) := by
  obtain ⟨e, _, heG, _, he, _⟩ := membership_graph_identity_decoration base Q.transitive
  have hmask : Q.masks = P.masks := base.extensional _ _
    (fun i => (Q.maskMembers i).trans (P.maskMembers i).symm)
  let G : CodedMaskGraphAction base P Q.domain e :=
    ⟨Q.family, hmask ▸ Q.familyFunction, Q.maps, Q.mapCodes,
      fun i => (graph_iso_membership_iff he he).mpr (Q.iso i), Q.one, Q.mul⟩
  have hExt : GraphExtensionalCode s Q.domain e := by
    intro x hx y hy hr
    apply base.extensional
    intro z
    constructor
    · intro hz
      exact ((he y z).mp ((hr z (Q.transitive x hx z hz)).mp ((he x z).mpr ⟨hx, hz⟩))).2
    · intro hz
      exact ((he x z).mp ((hr z (Q.transitive y hy z hz)).mpr ((he y z).mpr ⟨hy, hz⟩))).2
  have hEnd : EndExtensionCode s Q.domain e t :=
    ⟨htQ, fun x hx y => (he x y).trans ⟨fun h => h.2, fun h => ⟨htQ x hx, h⟩⟩⟩
  obtain ⟨C, f, hPC, hm, hf, hfi, hfix, hvals, hOld, hInt⟩ :=
    bafa_joint_graph_attachment base hB P G ht htP heG hExt hEnd hstable hag
  obtain ⟨T, E, hT, _, hE, hiso⟩ := injective_decoration_graph_iso base hf hfi
  have hmem := (graph_iso_membership_iff he hE).mp hiso
  have hTC : Subset s T C.domain := by
    intro X hX
    obtain ⟨x, _, hxX⟩ := (hmem.2.2.1 X).mp hX
    exact hvals x X hxX
  exact ⟨C, f, hPC, hm, hOld, ⟨⟨T, hT, hTC, hmem, hInt⟩⟩, hfix⟩

/-- Two different extensions of one action can be placed in a common
    extension, with the first kept literal and the second fixed on the base. -/
theorem bafa_coded_mask_two_extensions (base : BaseCollection s) (hB : BAFACode s)
    {w : U} (A P Q : CodedMaskAction base w)
    (hAP : Subset s A.domain P.domain) (hAQ : Subset s A.domain Q.domain)
    (hP : ∀ i x y, CodedRelation s (A.maps i) x y → CodedRelation s (P.maps i) x y)
    (hQ : ∀ i x y, CodedRelation s (A.maps i) x y → CodedRelation s (Q.maps i) x y) :
    ∃ C : CodedMaskAction base w, ∃ f,
      Subset s P.domain C.domain ∧ C.masks = P.masks ∧
      (∀ i x y, CodedRelation s (P.maps i) x y → CodedRelation s (C.maps i) x y) ∧
      Nonempty (CodedMaskEmbedding base Q C f) ∧ (∀ x, s x A.domain → CodedRelation s f x x) := by
  have hback : ∀ i x y, s x A.domain → CodedRelation s (P.maps i) x y → CodedRelation s (A.maps i) x y := by
    intro i x y hx hxy
    obtain ⟨z, hxz, _⟩ := (A.iso i).1.2 x hx
    exact (coded_function_value_unique (P.iso i).1 (hP i x z hxz) hxy) ▸ hxz
  apply bafa_coded_mask_amalgamation base hB P Q A.transitive hAP hAQ
  · intro i x y hx hxy
    exact ((A.iso i).2.2.1 y).mpr ⟨x, hx, hback i x y hx hxy⟩
  · intro i x y hx
    refine ⟨fun hxy => hQ i x y (hback i x y hx hxy), ?_⟩
    intro hxy
    obtain ⟨z, hxz, _⟩ := (A.iso i).1.2 x hx
    exact (coded_function_value_unique (Q.iso i).1 (hQ i x z hxz) hxy) ▸ hP i x z hxz

#print axioms bafa_coded_mask_amalgamation
end FullBridge
