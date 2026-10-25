import JointClassification
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- An actual joint representative set with a total node classifier. Repeated
    representatives are permitted precisely when their quotient images agree. -/
structure PrunedJointRealization (base : BaseCollection s) (b : U)
    {A : PrunedQuotient base b} (P : PrunedNodePresentation base b A) (e : U) where
  carrier : U
  classifier : U
  function : FunctionCode s carrier classifier
  retained : ∀ v, s v carrier → ¬s b v
  closed : ∀ v, s v carrier → ∀ w, PrunedMember s b v w → s w carrier
  range : ∀ v c, CodedRelation s classifier v c → s c P.nodes
  onto : ∀ c, s c P.nodes → ∃ v, CodedRelation s classifier v c
  kernel : ∀ v w c d, CodedRelation s classifier v c → CodedRelation s classifier w d →
    (c = d ↔ prunedCode base b v = prunedCode base b w)
  rows : ∀ v c, s v carrier → CodedRelation s classifier v c → ∀ d, s d P.nodes →
    (CodedRelation s e c d ↔ ∃ w, PrunedMember s b v w ∧ CodedRelation s classifier w d)

/-- The joint realization and every classifier condition are constructed from
    the target end-extension, not postulated as a BAFA-solving interface. -/
theorem pruned_fixed_joint_realization (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) {b : U} (hb : SelfSingleton s b)
    {T A R : PrunedQuotient base b} (hT : TransitiveCode (prunedMember base b) T)
    (P : PrunedNodePresentation base b A) {e : U}
    (he : ∀ c d X Y, PrunedNodeCorresponds P c X → PrunedNodeCorresponds P d Y →
      (CodedRelation s e c d ↔ CodedRelation (prunedMember base b) R X Y))
    (hExt : GraphExtensionalCode s P.nodes e)
    (hend : EndExtensionCode (prunedMember base b) A R T) :
    ∃ J : PrunedJointRealization base b P e,
      ∀ X, prunedMember base b X T → ∃ v c,
        prunedCode base b v = X ∧ CodedRelation s J.classifier v c ∧ PrunedNodeCorresponds P c X := by
  classical
  have hbb := (hb b).mpr rfl
  obtain ⟨C, h, hH, hh, hOld⟩ := pruned_fixed_cover_classification base hbb hT P he hend
  have hRange : ∀ v c, CodedRelation s h v c → s c P.nodes := by
    intro v c hvc
    obtain ⟨x, hx, hxc, _⟩ := ((hh v c).mp hvc).2
    exact (P.nodes_iff c).mpr ⟨x, hx, hxc⟩
  obtain ⟨a, ha⟩ := classification_complement_exists base P.nodes h
  have hSD : Subset s C.carrier C.surrounding := fun v hv => ((C.members_iff v).mp hv).1
  have hSgood : ∀ v, s v C.carrier → ¬s b v := fun v hv => ((C.members_iff v).mp hv).2.1
  obtain ⟨f, V, K, hf, hi, hV, hout, hK, hgood, hclosed, hNew⟩ :=
    pruned_joint_closed_realization base hF hb C.transitive hSD hSgood C.closed (a := a) (e := e) (h := h)
  have hdis : ∀ v, s v C.carrier → ¬s v V :=
    fun v hv hvV => hout v hvV (hSD v hv)
  obtain ⟨j, hjF, hj⟩ := joint_classification_exists base hH hf hi hV hK hdis
  have hcover : ∀ c, s c P.nodes → s c a ∨ ∃ v, CodedRelation s h v c := by
    intro c hc
    by_cases hx : ∃ v, CodedRelation s h v c
    · exact Or.inr hx
    · exact Or.inl ((ha c).mpr ⟨hc, hx⟩)
  have hJR : ∀ v c, CodedRelation s j v c → s c P.nodes := by
    intro v c hvc
    rcases (hj v c).mp hvc with hvc | hcv
    · exact hRange v c hvc
    · exact ((ha c).mp (coded_function_domain hf hcv)).1
  have hrows := joint_classification_rows hH hf hV hdis hjF hj hcover C.closed hOld hNew
  have hkernel : ∀ v w c d, CodedRelation s j v c → CodedRelation s j w d →
      (c = d ↔ prunedCode base b v = prunedCode base b w) := by
    intro v w c d hvc hwd
    exact joint_classification_quotient_kernel base hf hjF hj
      (fun c hc => ((ha c).mp hc).2)
      (fun v w c d hvc hwd => pruned_classification_kernel base P hh hvc hwd)
      hJR hclosed hExt hrows hvc hwd
  have honto : ∀ c, s c P.nodes → ∃ v, CodedRelation s j v c := by
    intro c hc
    rcases hcover c hc with hca | ⟨v, hvc⟩
    · obtain ⟨v, hcv, _⟩ := hf.2 c hca
      exact ⟨v, (hj v c).mpr (Or.inr hcv)⟩
    · exact ⟨v, (hj v c).mpr (Or.inl hvc)⟩
  let J : PrunedJointRealization base b P e :=
    ⟨K, j, hjF, hgood, hclosed, hJR, honto, hkernel, hrows⟩
  refine ⟨J, ?_⟩
  intro X hXT
  have hXC : prunedMember base b X (prunedCode base b C.carrier) := C.image.symm ▸ hXT
  obtain ⟨v, hv, hqv⟩ := ((pruned_good_row base hbb hSgood).2 X).mp hXC
  obtain ⟨c, hvc, _⟩ := hH.2 v hv
  refine ⟨v, c, hqv, (hj v c).mpr (Or.inl hvc), ?_⟩
  have hc := ((hh v c).mp hvc).2
  simpa only [hqv] using hc

#print axioms pruned_fixed_joint_realization
end FullBridge
