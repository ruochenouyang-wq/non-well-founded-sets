import JointOrbitRealizations
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem countable_bafa_transitive_joint_extension (base : BaseCollection s) (hB : BAFACode s) {w : U}
    (A : CodedMaskAction base w) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : InternalMask s w → U → U,
      (∀ a, ElementaryMap s s (J a) ∧ (∀ y, ∃ x, J a x = y) ∧ LocallyInternalTransitiveMap s (J a)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ a b x, J (internalMaskMul base a b) x = J a (J b x)) ∧
      (∀ a x y, CodedRelation s (A.maps a) x y → J a x = y) ∧
      (∀ a x, internalCode base (J a x) = internalCode base x) ∧
      (∀ d, ∃ t, TransitiveCode s t ∧ Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) := by
  obtain ⟨C, hC⟩ := enumerated_coded_mask_chain base hB A enum henum
  refine ⟨codedMaskChainMap base C, ?_, coded_mask_chain_identity base C,
    coded_mask_chain_multiplication base C, ?_, ?_, coded_mask_chain_transitive_joint_covers base C⟩
  · intro a
    exact ⟨bijective_membership_elementary _ (iso_chain_map_injective (C.isoChain base a))
      (iso_chain_map_surjective (C.isoChain base a)) (iso_chain_map_members (C.isoChain base a)),
      iso_chain_map_surjective (C.isoChain base a), iso_chain_map_local (C.isoChain base a)⟩
  · intro a x y hxy
    apply iso_chain_map_value (C.isoChain base a)
    refine ⟨0, ?_⟩
    change CodedRelation s ((C.stage 0).maps a) x y
    rw [hC]
    exact hxy
  · intro a x
    exact (internal_code_eq base _ x).mpr
      (locally_internal_map_behavior base _ (iso_chain_map_local (C.isoChain base a)) x)

theorem hereditary_mask_agreement_on_transitive {w A x : U}
    {J K : InternalMask s w → U → U} (hA : TransitiveCode s A) (hx : s x A)
    (hAgree : ∀ i y, s y A → J i y = K i y) :
    HereditarilyMaskSupported s w J x ↔ HereditarilyMaskSupported s w K x := by
  have htransfer : ∀ {L M : InternalMask s w → U → U},
      (∀ i y, s y A → L i y = M i y) →
      HereditarilyMaskSupported s w L x → HereditarilyMaskSupported s w M x := by
    intro L M hLM h y hxy
    obtain ⟨N, hN, hfix⟩ := h y hxy
    exact ⟨N, hN, fun i hi => (hLM i y (descendant_in_transitive hA hx hxy)).symm.trans (hfix i hi)⟩
  exact ⟨htransfer hAgree, htransfer (fun i y hy => (hAgree i y hy).symm)⟩

/-- Keeping the raw orbit nodes in the old domain makes graph equivariance
    agree with the final universe action on inputs as well as values. -/
theorem countable_joint_orbit_global_extension (base : BaseCollection s) (hBAFA : BAFACode s)
    {z w O : U} (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (P : CodedMaskAction base w) (D : CodedOrbitDiagram base w J O)
    (R : JointOrbitRealization base P D) (hNP : Subset s D.domain P.domain)
    (hOP : Subset s O P.domain)
    (hP : ∀ i x y, CodedRelation s (P.maps i) x y ↔ s x P.domain ∧ J i x = y)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J' : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J' i) ∧ (∀ y, ∃ x, J' i x = y) ∧ LocallyInternalTransitiveMap s (J' i)) ∧
      (∀ x, J' (internalMaskOne base w) x = x) ∧
      (∀ i j x, J' (internalMaskMul base i j) x = J' i (J' j x)) ∧
      (∀ i x y, CodedRelation s (P.maps i) x y → J' i x = y) ∧
      (∀ d, ∃ t, TransitiveCode s t ∧ Nonempty (JointMaskDomain s w J' t) ∧ Subset s d t) ∧
      (∀ i x X, CodedRelation s R.function x X → CodedRelation s R.function (J' i x) (J' i X)) ∧
      (∀ x, s x P.domain → (HereditarilyMaskSupported s w J' x ↔ HereditarilyMaskSupported s w J x)) ∧
      ∀ p t a r, s p O → OrbitGraphParameters s p t a r →
        HereditarilyMaskSupported s w J t → HereditarilyMaskSupported s w J a →
        HereditarilyMaskSupported s w J r →
        ∃ f, DecorationCode s a r f ∧ InjectiveCode s f ∧
          (∀ x, s x t → CodedRelation s f x x) ∧ HereditarilyMaskSupported s w J' f ∧
          ∀ x X, CodedRelation s f x X → HereditarilyMaskSupported s w J' X := by
  obtain ⟨J', hJ', hOne, hMul, hRJ, _, hCover⟩ :=
    countable_bafa_transitive_joint_extension base hBAFA R.action enum henum
  have hPJ : ∀ i x y, CodedRelation s (P.maps i) x y → J' i x = y :=
    fun i x y hxy => hRJ i x y (R.extendsOld.2 i x y hxy)
  have heq : ∀ i x X, CodedRelation s R.function x X →
      CodedRelation s R.function (J' i x) (J' i X) := by
    intro i x X hxX
    have hx := coded_function_domain R.solution.1 hxX
    obtain ⟨y, hxy, _⟩ := (D.iso i).1.2 x hx
    have hy := graph_iso_value (D.iso i) hxy
    obtain ⟨Y, hyY, _⟩ := R.solution.1.2 y hy
    have hXY := R.equivariant i x y X Y hxy hxX hyY
    have hpxy := (hP i x y).mpr ⟨hNP x hx,
      (((D.joint.graphs i (D.maps i) (D.mapCodes i)).2 x y).mp hxy).2⟩
    rw [hPJ i x y hpxy, hRJ i X Y hXY]
    exact hyY
  have hs : ∀ i x, J' i (J' i x) = x := by
    intro i x
    have h := hMul i i x
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (hOne x)
  have hAgree : ∀ i x, s x P.domain → J' i x = J i x := by
    intro i x hx
    exact hPJ i x (J i x) ((hP i x (J i x)).mpr ⟨hx, rfl⟩)
  have hH : ∀ x, s x P.domain → (HereditarilyMaskSupported s w J' x ↔ HereditarilyMaskSupported s w J x) :=
    fun x hx => hereditary_mask_agreement_on_transitive P.transitive hx hAgree
  refine ⟨J', hJ', hOne, hMul, hPJ, hCover, heq, hH, ?_⟩
  intro p t a r hp hpar htH haH hrH
  have hparP := orbit_graph_parameters_in_transitive P.transitive (hOP p hp) hpar
  have htH' := (hH t hparP.1).mpr htH
  have haH' := (hH a hparP.2.1).mpr haH
  have hrH' := (hH r hparP.2.2).mpr hrH
  obtain ⟨C, f, hf, hi, hfix, hfr⟩ := R.requests p t a r hp hpar
  obtain ⟨hfH, hvalues⟩ := orbit_component_pullback_hereditary base hw (fun i => (hJ' i).1) hs
    C hpar htH' haH' hrH' hf hfr heq
  exact ⟨f, hf, hi, hfix, hfH, hvalues⟩

/-- Enlarge an actual joint transitive bound before attachment, retaining
    the whole raw node set, all parameters, and any prescribed source set L. -/
theorem joint_orbit_stage_exists (base : BaseCollection s) (hBAFA : BAFACode s)
    {w O : U} {J : InternalMask s w → U → U} (D : CodedOrbitDiagram base w J O)
    (hj : ∀ i, ElementaryMap s s (J i)) (hs : ∀ i x, J i (J i x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ B, TransitiveCode s B ∧ Nonempty (JointMaskDomain s w J B) ∧ Subset s d B)
    (hO : ∀ i p, s p O → s (J i p) O) (hReq : ∀ p, s p O → BafaRequestCode s p)
    (L : U) :
    ∃ P : CodedMaskAction base w, Subset s D.domain P.domain ∧ Subset s O P.domain ∧
      Subset s L P.domain ∧
      (∀ i x y, CodedRelation s (P.maps i) x y ↔ s x P.domain ∧ J i x = y) ∧
      Nonempty (JointOrbitRealization base P D) := by
  obtain ⟨S, hS⟩ := binary_union_exists base.pairing base.union D.domain O
  obtain ⟨S', hS'⟩ := binary_union_exists base.pairing base.union S L
  obtain ⟨B, hB, ⟨A⟩, hSB⟩ := hCover S'
  obtain ⟨P, hPB, _, _, hP⟩ := joint_mask_coded_action base A hB hj hs hOne hMul
  have hNP : Subset s D.domain P.domain := by
    intro x hx
    rw [hPB]
    exact hSB x ((hS' x).mpr (Or.inl ((hS x).mpr (Or.inl hx))))
  have hOP : Subset s O P.domain := by
    intro x hx
    rw [hPB]
    exact hSB x ((hS' x).mpr (Or.inl ((hS x).mpr (Or.inr hx))))
  have hLP : Subset s L P.domain := by
    intro x hx
    rw [hPB]
    exact hSB x ((hS' x).mpr (Or.inr hx))
  have hP' : ∀ i x y, CodedRelation s (P.maps i) x y ↔ s x P.domain ∧ J i x = y := by
    intro i x y
    rw [hPB]
    exact hP i x y
  exact ⟨P, hNP, hOP, hLP, hP', bafa_joint_orbit_realization base hBAFA P D hj hOP hO hReq hP'⟩

/-- Actual extension solving every formerly supported request of one orbit,
    while retaining any prescribed source region L and its support status. -/
theorem countable_bafa_supported_orbit_extension (base : BaseCollection s) (hBAFA : BAFACode s)
    {z w O : U} (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (D : CodedOrbitDiagram base w J O)
    (hj : ∀ i, ElementaryMap s s (J i)) (hs : ∀ i x, J i (J i x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ B, TransitiveCode s B ∧ Nonempty (JointMaskDomain s w J B) ∧ Subset s d B)
    (hO : ∀ i p, s p O → s (J i p) O) (hReq : ∀ p, s p O → BafaRequestCode s p)
    (L : U) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J' : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J' i) ∧ (∀ y, ∃ x, J' i x = y) ∧ LocallyInternalTransitiveMap s (J' i)) ∧
      (∀ x, J' (internalMaskOne base w) x = x) ∧
      (∀ i j x, J' (internalMaskMul base i j) x = J' i (J' j x)) ∧
      (∀ i x, s x L → J' i x = J i x) ∧
      (∀ d, ∃ t, TransitiveCode s t ∧ Nonempty (JointMaskDomain s w J' t) ∧ Subset s d t) ∧
      (∀ x, s x L → (HereditarilyMaskSupported s w J' x ↔ HereditarilyMaskSupported s w J x)) ∧
      ∀ p t a r, s p O → OrbitGraphParameters s p t a r →
        HereditarilyMaskSupported s w J t → HereditarilyMaskSupported s w J a →
        HereditarilyMaskSupported s w J r →
        ∃ f, DecorationCode s a r f ∧ InjectiveCode s f ∧
          (∀ x, s x t → CodedRelation s f x x) ∧ HereditarilyMaskSupported s w J' f ∧
          ∀ x X, CodedRelation s f x X → HereditarilyMaskSupported s w J' X := by
  obtain ⟨P, hNP, hOP, hLP, hP, ⟨R⟩⟩ := joint_orbit_stage_exists base hBAFA D hj hs hOne hMul hCover hO hReq L
  obtain ⟨J', hJ', hOne', hMul', hPJ, hCover', _, hH, hSolutions⟩ :=
    countable_joint_orbit_global_extension base hBAFA hw P D R hNP hOP hP enum henum
  refine ⟨J', hJ', hOne', hMul', ?_, hCover', fun x hx => hH x (hLP x hx), hSolutions⟩
  intro i x hx
  exact hPJ i x (J i x) ((hP i x (J i x)).mpr ⟨hLP x hx, rfl⟩)

#print axioms countable_joint_orbit_global_extension
#print axioms joint_orbit_stage_exists
end FullBridge
