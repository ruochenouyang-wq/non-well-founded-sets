import JointTaggedSolutions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def jointClassificationFormula : Formula 4 :=
  (relatedFormula 2 1 0).disj (relatedFormula 3 0 1)

theorem eval_jointClassificationFormula (h f v c : U) :
    Eval s jointClassificationFormula (cons c (cons v (cons h (cons f Fin.elim0)))) ↔
      CodedRelation s h v c ∨ CodedRelation s f c v := by
  simp only [jointClassificationFormula, eval_disj, eval_relatedFormula]
  rfl

/-- New nodes are the actual internal complement of the old classification range. -/
theorem classification_complement_exists (base : BaseCollection s) (A h : U) :
    ∃ a, ∀ c, s c a ↔ s c A ∧ ¬∃ v, CodedRelation s h v c := by
  obtain ⟨a, ha⟩ := base.separation 1
    (.impl (.ex (relatedFormula 2 0 1)) .bottom) (cons h Fin.elim0) A
  refine ⟨a, ?_⟩
  intro c
  have hv := ha c
  simp only [Eval, eval_relatedFormula] at hv
  exact hv

/-- Unite an old classification with the inverse of a fresh injective solution.
    Old classification values may repeat, but old/new source domains are disjoint. -/
theorem joint_classification_exists (base : BaseCollection s) {S a h f V C : U}
    (hH : FunctionCode s S h) (hF : FunctionCode s a f) (hI : InjectiveCode s f)
    (hV : RangeCode s a f V) (hC : ∀ v, s v C ↔ s v S ∨ s v V)
    (hdis : ∀ v, s v S → ¬s v V) :
    ∃ J, FunctionCode s C J ∧ ∀ v c, CodedRelation s J v c ↔
      CodedRelation s h v c ∨ CodedRelation s f c v := by
  obtain ⟨d, hd⟩ := codedRelation_component_bound base.union h
  obtain ⟨e, he⟩ := codedRelation_component_bound base.union f
  obtain ⟨u, hu⟩ := binary_union_exists base.pairing base.union d e
  obtain ⟨J, hmem⟩ := relation_comprehension_members base jointClassificationFormula
    (cons h (cons f Fin.elim0)) u
  have hJ : ∀ v c, CodedRelation s J v c ↔ CodedRelation s h v c ∨ CodedRelation s f c v := by
    intro v c
    constructor
    · rintro ⟨p, hp, hpvc⟩
      obtain ⟨v', c', _, _, hp', hev⟩ := (hmem p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpvc hp'
      exact (eval_jointClassificationFormula h f v c).mp hev
    · intro hv
      have hb : s v u ∧ s c u := by
        rcases hv with hv | hv
        · exact ⟨(hu v).mpr (Or.inl (hd v c hv).1), (hu c).mpr (Or.inl (hd v c hv).2)⟩
        · exact ⟨(hu v).mpr (Or.inr (he c v hv).2), (hu c).mpr (Or.inr (he c v hv).1)⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing v c
      exact ⟨p, (hmem p).mpr ⟨v, c, hb.1, hb.2, hp,
        (eval_jointClassificationFormula h f v c).mpr hv⟩, hp⟩
  have hin : ∀ c v, CodedRelation s f c v → s v V :=
    fun c v hcv => (hV v).mpr ⟨c, coded_function_domain hF hcv, hcv⟩
  refine ⟨J, ⟨?_, ?_⟩, hJ⟩
  · intro p hp
    obtain ⟨v, c, _, _, hpvc, hev⟩ := (hmem p).mp hp
    refine ⟨v, c, (hC v).mpr ?_, hpvc⟩
    rcases (eval_jointClassificationFormula h f v c).mp hev with hv | hv
    · exact Or.inl (coded_function_domain hH hv)
    · exact Or.inr (hin c v hv)
  · intro v hv
    rcases (hC v).mp hv with hvS | hvV
    · obtain ⟨c, hvc, _⟩ := hH.2 v hvS
      refine ⟨c, (hJ v c).mpr (Or.inl hvc), ?_⟩
      intro d hvd
      rcases (hJ v d).mp hvd with hd | hd
      · exact coded_function_value_unique hH hd hvc
      · exact False.elim (hdis v hvS (hin d v hd))
    · obtain ⟨c, _, hcv⟩ := (hV v).mp hvV
      refine ⟨c, (hJ v c).mpr (Or.inr hcv), ?_⟩
      intro d hvd
      rcases (hJ v d).mp hvd with hd | hd
      · exact False.elim (hdis v (coded_function_domain hH hd) hvV)
      · exact hI d c v hd hcv

/-- Exact old and new successor equations become one exact classification map. -/
theorem joint_classification_rows {b A a e S h f V C J : U}
    (hH : FunctionCode s S h) (hF : FunctionCode s a f)
    (hV : RangeCode s a f V) (hdis : ∀ v, s v S → ¬s v V)
    (hJ : FunctionCode s C J)
    (hJrel : ∀ v c, CodedRelation s J v c ↔ CodedRelation s h v c ∨ CodedRelation s f c v)
    (hcover : ∀ d, s d A → s d a ∨ ∃ y, CodedRelation s h y d)
    (hclosed : ∀ v, s v S → ∀ w, PrunedMember s b v w → s w S)
    (hOld : ∀ v c, s v S → CodedRelation s h v c → ∀ d, s d A →
      (CodedRelation s e c d ↔ ∃ w, PrunedMember s b v w ∧ CodedRelation s h w d))
    (hNew : ∀ c v, s c a → CodedRelation s f c v → ∀ w,
      PrunedMember s b v w ↔
        (∃ d, s d a ∧ CodedRelation s e c d ∧ CodedRelation s f d w) ∨
        (s w S ∧ ∃ d, CodedRelation s h w d ∧ CodedRelation s e c d)) :
    ∀ v c, s v C → CodedRelation s J v c → ∀ d, s d A →
      (CodedRelation s e c d ↔ ∃ w, PrunedMember s b v w ∧ CodedRelation s J w d) := by
  have hin : ∀ d w, CodedRelation s f d w → s w V :=
    fun d w hdw => (hV w).mpr ⟨d, coded_function_domain hF hdw, hdw⟩
  intro v c _ hvc d hd
  rcases (hJrel v c).mp hvc with hvc | hcv
  · have hvS := coded_function_domain hH hvc
    refine (hOld v c hvS hvc d hd).trans ⟨?_, ?_⟩
    · rintro ⟨w, hvw, hwd⟩
      exact ⟨w, hvw, (hJrel w d).mpr (Or.inl hwd)⟩
    · rintro ⟨w, hvw, hwd⟩
      rcases (hJrel w d).mp hwd with hwd | hdw
      · exact ⟨w, hvw, hwd⟩
      · exact False.elim (hdis w (hclosed v hvS w hvw) (hin d w hdw))
  · have hc := coded_function_domain hF hcv
    constructor
    · intro hcd
      rcases hcover d hd with hda | ⟨w, hwd⟩
      · obtain ⟨w, hdw, _⟩ := hF.2 d hda
        exact ⟨w, (hNew c v hc hcv w).mpr (Or.inl ⟨d, hda, hcd, hdw⟩),
          (hJrel w d).mpr (Or.inr hdw)⟩
      · exact ⟨w, (hNew c v hc hcv w).mpr (Or.inr ⟨coded_function_domain hH hwd, d, hwd, hcd⟩),
          (hJrel w d).mpr (Or.inl hwd)⟩
    · rintro ⟨w, hvw, hwd⟩
      rcases (hNew c v hc hcv w).mp hvw with ⟨k, _, hck, hkw⟩ | ⟨_, k, hwk, hck⟩
      · have hkd := coded_function_value_unique hJ ((hJrel w k).mpr (Or.inr hkw)) hwd
        exact hkd ▸ hck
      · have hkd := coded_function_value_unique hJ ((hJrel w k).mpr (Or.inl hwk)) hwd
        exact hkd ▸ hck

/-- Equality of joint classification values is exactly equality in the actual
    pruned quotient, once the old classifier has that kernel. -/
theorem joint_classification_quotient_kernel (base : BaseCollection s) {b A a e h f C J : U}
    (hF : FunctionCode s a f) (hJ : FunctionCode s C J)
    (hJrel : ∀ v c, CodedRelation s J v c ↔ CodedRelation s h v c ∨ CodedRelation s f c v)
    (hnew : ∀ c, s c a → ¬∃ v, CodedRelation s h v c)
    (hOldKernel : ∀ v w c d, CodedRelation s h v c → CodedRelation s h w d →
      (c = d ↔ prunedCode base b v = prunedCode base b w))
    (hRange : ∀ v c, CodedRelation s J v c → s c A)
    (hClosed : ∀ v, s v C → ∀ w, PrunedMember s b v w → s w C)
    (hExt : GraphExtensionalCode s A e)
    (hRows : ∀ v c, s v C → CodedRelation s J v c → ∀ d, s d A →
      (CodedRelation s e c d ↔ ∃ w, PrunedMember s b v w ∧ CodedRelation s J w d))
    {v w c d : U} (hvc : CodedRelation s J v c) (hwd : CodedRelation s J w d) :
    c = d ↔ prunedCode base b v = prunedCode base b w := by
  constructor
  · intro hcd
    subst d
    rcases (hJrel v c).mp hvc with hvc | hcv <;> rcases (hJrel w c).mp hwd with hwc | hcw
    · exact (hOldKernel v w c c hvc hwc).mp rfl
    · exact False.elim (hnew c (coded_function_domain hF hcw) ⟨v, hvc⟩)
    · exact False.elim (hnew c (coded_function_domain hF hcv) ⟨w, hwc⟩)
    · exact congrArg (prunedCode base b) (coded_function_value_unique hF hcv hcw)
  · exact pruned_code_conserves_closed_map base hJ hRange hClosed hExt hRows hvc hwd

#print axioms joint_classification_quotient_kernel
end FullBridge
