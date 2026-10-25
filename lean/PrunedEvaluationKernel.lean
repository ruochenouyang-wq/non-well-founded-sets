import PrunedEvaluationMap
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def retainedFunctionKernelFormula : Formula 4 :=
  .conj (.impl (.member 2 1) .bottom) (.conj (.impl (.member 2 0) .bottom)
    (.ex (.conj (relatedFormula 4 2 0) (relatedFormula 4 1 0))))

theorem eval_retainedFunctionKernelFormula (b f x y : U) :
    Eval s retainedFunctionKernelFormula (cons y (cons x (cons b (cons f Fin.elim0)))) ↔
      ¬s b x ∧ ¬s b y ∧ ∃ z, CodedRelation s f x z ∧ CodedRelation s f y z := by
  simp only [retainedFunctionKernelFormula, Eval, eval_relatedFormula]
  rfl

theorem pruned_evaluation_kernel_code (base : BaseCollection s) (hA : AFACode s) (b c : U) :
    ∃ r, RetainedRelationCode s b r ∧ ∀ x y, CodedRelation s r x y ↔
      s x c ∧ s y c ∧ ¬s b x ∧ ¬s b y ∧
        prunedEvaluationMap base hA b (prunedCode base b x) =
        prunedEvaluationMap base hA b (prunedCode base b y) := by
  obtain ⟨f, _, hf⟩ := canonical_graph_value_function base hA prunedMemberFormula
    (cons b Fin.elim0) (pruned_edges_are_members b) c
  obtain ⟨r, hG, hr⟩ := normalized_relation_comprehension base retainedFunctionKernelFormula
    (cons b (cons f Fin.elim0)) c
  have hr' : ∀ x y, CodedRelation s r x y ↔ s x c ∧ s y c ∧ ¬s b x ∧ ¬s b y ∧
      prunedEvaluationMap base hA b (prunedCode base b x) =
      prunedEvaluationMap base hA b (prunedCode base b y) := by
    intro x y
    have hv := hr x y
    rw [eval_retainedFunctionKernelFormula] at hv
    refine hv.trans ⟨?_, ?_⟩
    · rintro ⟨hx, hy, hxg, hyg, z, hxz, hyz⟩
      exact ⟨hx, hy, hxg, hyg, ((hf x z).mp hxz).2.trans ((hf y z).mp hyz).2.symm⟩
    · rintro ⟨hx, hy, hxg, hyg, heq⟩
      exact ⟨hx, hy, hxg, hyg, _, (hf x _).mpr ⟨hx, rfl⟩, (hf y _).mpr ⟨hy, heq.symm⟩⟩
  refine ⟨r, ?_, hr'⟩
  intro p hp
  obtain ⟨x, y, _, _, hpxy⟩ := hG p hp
  have h := (hr' x y).mp ⟨p, hp, hpxy⟩
  exact ⟨x, y, h.2.2.1, h.2.2.2.1, hpxy⟩

/-- Equality of evaluation has a genuine internal target bisimulation witness,
    obtained by projecting an actual bounded retained source kernel relation. -/
theorem pruned_equal_evaluation_internal_behavior (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hbb : s b b) {X Y : PrunedQuotient base b}
    (hXY : prunedEvaluationMap base hA b X = prunedEvaluationMap base hA b Y) :
    InternalBehavior (prunedMember base b) X Y := by
  obtain ⟨x, hxg, rfl⟩ := pruned_good_representative base b X
  obtain ⟨y, hyg, rfl⟩ := pruned_good_representative base b Y
  obtain ⟨a, ha, hxa⟩ := transitive_sets_cover base x
  obtain ⟨d, hd, hyd⟩ := transitive_sets_cover base y
  obtain ⟨c, hc, hac, hdc⟩ := transitive_sets_directed base ha hd
  obtain ⟨r, hret, hr⟩ := pruned_evaluation_kernel_code base hA b c
  have hImage := pruned_coded_relation_image base hbb hret
  have hsym : ∀ u v, CodedRelation s r u v → CodedRelation s r v u := by
    intro u v huv
    obtain ⟨hu, hv, hug, hvg, heq⟩ := (hr u v).mp huv
    exact (hr v u).mpr ⟨hv, hu, hvg, hug, heq.symm⟩
  have hqsym : ∀ U V, CodedRelation (prunedMember base b) (prunedCode base b r) U V →
      CodedRelation (prunedMember base b) (prunedCode base b r) V U := by
    intro U V hUV
    obtain ⟨u, v, huv, hqu, hqv⟩ := (hImage U V).mp hUV
    exact (hImage V U).mpr ⟨v, u, hsym u v huv, hqv, hqu⟩
  have hmatch : ∀ u v, CodedRelation s r u v → ∀ Z,
      prunedMember base b Z (prunedCode base b u) → ∃ W,
        prunedMember base b W (prunedCode base b v) ∧
        CodedRelation (prunedMember base b) (prunedCode base b r) Z W := by
    intro u v huv Z hZu
    obtain ⟨hu, hv, _, _, heq⟩ := (hr u v).mp huv
    obtain ⟨z, huz, hqz⟩ := (least_global_exact_members base prunedMemberFormula
      (cons b Fin.elim0) (pruned_edges_are_members b) u Z).mp hZu
    have hzd : s (prunedEvaluationMap base hA b (prunedCode base b z))
        (prunedEvaluationMap base hA b (prunedCode base b u)) :=
      (canonical_graph_value_rows base hA prunedMemberFormula (cons b Fin.elim0)
        (pruned_edges_are_members b) u _).mpr ⟨z, huz, rfl⟩
    have hzv := heq ▸ hzd
    obtain ⟨w, hvw, hew⟩ := (canonical_graph_value_rows base hA prunedMemberFormula
      (cons b Fin.elim0) (pruned_edges_are_members b) v _).mp hzv
    refine ⟨prunedCode base b w,
      (least_global_exact_members base prunedMemberFormula (cons b Fin.elim0)
        (pruned_edges_are_members b) v _).mpr ⟨w, hvw, rfl⟩, ?_⟩
    exact (hImage Z _).mpr ⟨z, w, (hr z w).mpr
      ⟨hc u hu z huz.2.2, hc v hv w hvw.2.2, huz.2.1, hvw.2.1, hew.symm⟩, hqz, rfl⟩
  have hBis : Bisimulation (prunedMember base b)
      (CodedRelation (prunedMember base b) (prunedCode base b r)) := by
    intro U V hUV
    obtain ⟨u, v, huv, rfl, rfl⟩ := (hImage U V).mp hUV
    constructor
    · exact hmatch u v huv
    · intro Z hZv
      obtain ⟨W, hWu, hZW⟩ := hmatch v u (hsym u v huv) Z hZv
      exact ⟨W, hWu, hqsym Z W hZW⟩
  apply coded_bisimulation_internalBehavior hBis
  exact (hImage _ _).mpr ⟨x, y, (hr x y).mpr ⟨hac x hxa, hdc y hyd, hxg, hyg, hXY⟩, rfl, rfl⟩

#print axioms pruned_equal_evaluation_internal_behavior
end FullBridge
