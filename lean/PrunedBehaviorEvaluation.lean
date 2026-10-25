import AfaInternalCoinduction
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Free variables [y,x,f,S,r,b]. Both witnesses are bounded by S. -/
def prunedBehaviorImageFormula : Formula 6 :=
  .ex (.ex (.conj (.member 1 5) (.conj (.member 0 5)
    (.conj (relatedFormula 4 1 3) (.conj (relatedFormula 4 0 2)
      (.disj (prunedEqualAtFormula 7 1 0) (prunedRelatedFormula 7 6 1 0)))))))

theorem eval_prunedBehaviorImageFormula (base : BaseCollection s) (b r S f x y : U) :
    Eval s prunedBehaviorImageFormula (cons y (cons x (cons f (cons S (cons r (cons b Fin.elim0)))))) ↔
      ∃ u v, s u S ∧ s v S ∧ CodedRelation s f u x ∧ CodedRelation s f v y ∧
        WithIdentity (CodedRelation (prunedMember base b) (prunedCode base b r))
          (prunedCode base b u) (prunedCode base b v) := by
  simp only [prunedBehaviorImageFormula, eval_disj, Eval, eval_relatedFormula,
    eval_prunedEqualAtFormula base, eval_prunedRelatedFormula base]
  rfl

theorem pruned_behavior_image_code (base : BaseCollection s) (b r S f : U) :
    ∃ H, ∀ x y, CodedRelation s H x y ↔
      ∃ u v, s u S ∧ s v S ∧ CodedRelation s f u x ∧ CodedRelation s f v y ∧
        WithIdentity (CodedRelation (prunedMember base b) (prunedCode base b r))
          (prunedCode base b u) (prunedCode base b v) := by
  obtain ⟨V, hV⟩ := coded_image_set_exists base f S
  obtain ⟨H, _, hH⟩ := normalized_relation_comprehension base prunedBehaviorImageFormula
    (cons f (cons S (cons r (cons b Fin.elim0)))) V
  refine ⟨H, fun x y => ?_⟩
  rw [hH, eval_prunedBehaviorImageFormula]
  constructor
  · exact fun h => h.2.2
  · intro h
    obtain ⟨u, v, hu, hv, hux, hvy, huv⟩ := h
    exact ⟨(hV x).mpr ⟨u, hu, hux⟩, (hV y).mpr ⟨v, hv, hvy⟩, u, v, hu, hv, hux, hvy, huv⟩

/-- The image relation is an actual source set, not an externally postulated
    bisimulation. Its bound is a fixed cover of a target transitive set. -/
theorem pruned_internal_behavior_equal_evaluation (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hbb : s b b) {X Y : PrunedQuotient base b}
    (hXY : InternalBehavior (prunedMember base b) X Y) :
    prunedEvaluationMap base hA b X = prunedEvaluationMap base hA b Y := by
  obtain ⟨R, hRB, hRXY⟩ := hXY
  obtain ⟨r, _, rfl⟩ := pruned_good_representative base b R
  let tb := pruned_quotient_base base hbb
  obtain ⟨A, hAtrans, hXA⟩ := transitive_sets_cover tb X
  obtain ⟨B, hBtrans, hYB⟩ := transitive_sets_cover tb Y
  obtain ⟨T, hT, hAT, hBT⟩ := transitive_sets_directed tb hAtrans hBtrans
  obtain ⟨C⟩ := pruned_fixed_cover_exists base hbb T hT
  obtain ⟨f, _, hf⟩ := canonical_graph_value_function base hA prunedMemberFormula
    (cons b Fin.elim0) (pruned_edges_are_members b) C.carrier
  obtain ⟨H, hH⟩ := pruned_behavior_image_code base b r C.carrier f
  let d := prunedEvaluationMap base hA b
  have hf' : ∀ u z, CodedRelation s f u z ↔ s u C.carrier ∧ d (prunedCode base b u) = z := hf
  have hrow := canonical_graph_value_rows base hA prunedMemberFormula
    (cons b Fin.elim0) (pruned_edges_are_members b)
  have hqrow := least_global_exact_members base prunedMemberFormula
    (cons b Fin.elim0) (pruned_edges_are_members b)
  have hBis : Bisimulation s (CodedRelation s H) := by
    intro z w hzw
    obtain ⟨u, v, hu, hv, huz, hvw, huv⟩ := (hH z w).mp hzw
    have hez := ((hf' u z).mp huz).2
    have hew := ((hf' v w).mp hvw).2
    constructor
    · intro z' hzz
      have hzdu : s z' (d (prunedCode base b u)) := hez.symm ▸ hzz
      obtain ⟨u', huu', heu'⟩ := (hrow u z').mp hzdu
      have hu' := C.closed u hu u' huu'
      obtain ⟨V', hV'v, hu'V'⟩ := (hRB _ _ huv).1 (prunedCode base b u')
        ((hqrow u _).mpr ⟨u', huu', rfl⟩)
      obtain ⟨v', hvv', hqv'⟩ := (hqrow v V').mp hV'v
      have hv' := C.closed v hv v' hvv'
      change prunedCode base b v' = V' at hqv'
      refine ⟨d (prunedCode base b v'), hew ▸ (hrow v _).mpr ⟨v', hvv', rfl⟩, ?_⟩
      exact (hH _ _).mpr ⟨u', v', hu', hv', (hf' _ _).mpr ⟨hu', heu'⟩,
        (hf' _ _).mpr ⟨hv', rfl⟩, hqv'.symm ▸ hu'V'⟩
    · intro w' hww
      have hwdv : s w' (d (prunedCode base b v)) := hew.symm ▸ hww
      obtain ⟨v', hvv', hev'⟩ := (hrow v w').mp hwdv
      have hv' := C.closed v hv v' hvv'
      obtain ⟨U', hU'u, hU'v'⟩ := (hRB _ _ huv).2 (prunedCode base b v')
        ((hqrow v _).mpr ⟨v', hvv', rfl⟩)
      obtain ⟨u', huu', hqu'⟩ := (hqrow u U').mp hU'u
      have hu' := C.closed u hu u' huu'
      change prunedCode base b u' = U' at hqu'
      refine ⟨d (prunedCode base b u'), hez ▸ (hrow u _).mpr ⟨u', huu', rfl⟩, ?_⟩
      exact (hH _ _).mpr ⟨u', v', hu', hv', (hf' _ _).mpr ⟨hu', rfl⟩,
        (hf' _ _).mpr ⟨hv', hev'⟩, hqu'.symm ▸ hU'v'⟩
  have hgood : ∀ u, s u C.carrier → ¬s b u := fun u hu => ((C.members_iff u).mp hu).2.1
  have hXcar : prunedMember base b X (prunedCode base b C.carrier) := C.image.symm ▸ hAT X hXA
  have hYcar : prunedMember base b Y (prunedCode base b C.carrier) := C.image.symm ▸ hBT Y hYB
  obtain ⟨x, hx, hqx⟩ := ((pruned_good_row base hbb hgood).2 X).mp hXcar
  obtain ⟨y, hy, hqy⟩ := ((pruned_good_row base hbb hgood).2 Y).mp hYcar
  have hxy : CodedRelation s H (d X) (d Y) := (hH _ _).mpr
    ⟨x, y, hx, hy, (hf' _ _).mpr ⟨hx, congrArg d hqx⟩,
      (hf' _ _).mpr ⟨hy, congrArg d hqy⟩, hqx.symm ▸ hqy.symm ▸ hRXY⟩
  exact (afa_internal_behavior_iff_equal base hA _ _).mp (coded_bisimulation_internalBehavior hBis hxy)

theorem pruned_evaluation_kernel_iff (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hbb : s b b) (X Y : PrunedQuotient base b) :
    InternalBehavior (prunedMember base b) X Y ↔
      prunedEvaluationMap base hA b X = prunedEvaluationMap base hA b Y :=
  ⟨pruned_internal_behavior_equal_evaluation base hA hbb,
   pruned_equal_evaluation_internal_behavior base hA hbb⟩

#print axioms pruned_evaluation_kernel_iff
end FullBridge
