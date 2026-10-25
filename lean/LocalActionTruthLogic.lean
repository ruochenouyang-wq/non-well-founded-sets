import LocalActionQuantifiers
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem action_covered_domain (base : BaseCollection s) {w x : U} {A : CodedMaskAction base w}
    (h : ActionCovered base A x) : s x A.domain := by
  obtain ⟨c, hc, _, hx, _⟩ := h
  exact hc x hx

theorem covered_action_environment_realized (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) {n} (v : Fin n → U) (hv : ∀ j, ActionCovered base A (v j)) :
    ∃ B : CodedMaskAction base w, ∃ f, ∃ _E : CodedMaskEmbedding base A B f,
      (∀ i x y, CodedRelation s (B.maps i) x y → J i x = y) ∧
      ∃ V : Fin n → CoveredMaskCarrier s w J, ∀ j, CodedRelation s f (v j) (V j).val := by
  classical
  obtain ⟨B, f, ⟨E⟩, hBJ⟩ := universal_any_action_realized base ctx A
  have ht : ∀ j, ∃ Y : CoveredMaskCarrier s w J, CodedRelation s f (v j) Y.val := by
    intro j
    obtain ⟨Y, hY, _⟩ := E.iso.1.2 (v j) (action_covered_domain base (hv j))
    have hcov := coded_mask_embedding_cover_forward base E hY (hv j)
    have hglobal := (action_covered_iff_global base B (coded_action_global_agreement base B hBJ)
      (coded_mask_embedding_value base E hY)).mp hcov
    exact ⟨⟨Y, hglobal⟩, hY⟩
  exact ⟨B, f, E, hBJ, (fun j => Classical.choose (ht j)), fun j => Classical.choose_spec (ht j)⟩

theorem local_action_truth_bounded (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) {n} (p : BoundedFormula n) (v : Fin n → U)
    (hv : ∀ j, ActionCovered base A (v j)) :
    LocalActionTruth base J p.toFormula A v ↔ BoundedEval s p v := by
  obtain ⟨B, f, E, hBJ, V, hV⟩ := covered_action_environment_realized base ctx A v hv
  exact (local_action_truth_realization_iff base ctx E hBJ p.toFormula v V hV).trans
    ((bounded_eval_toFormula p V).trans ((covered_mask_bounded_absoluteness p V).trans
      (coded_mask_embedding_bounded_semantics base E p v (fun j => (V j).val) hV).symm))

theorem local_action_truth_conj (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) {n} (p q : Formula n) (v : Fin n → U)
    (hv : ∀ j, ActionCovered base A (v j)) :
    LocalActionTruth base J (.conj p q) A v ↔ LocalActionTruth base J p A v ∧ LocalActionTruth base J q A v := by
  obtain ⟨B, f, E, hBJ, V, hV⟩ := covered_action_environment_realized base ctx A v hv
  rw [local_action_truth_realization_iff base ctx E hBJ (.conj p q) v V hV,
    local_action_truth_realization_iff base ctx E hBJ p v V hV,
    local_action_truth_realization_iff base ctx E hBJ q v V hV]
  rfl

theorem local_action_truth_impl (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) {n} (p q : Formula n) (v : Fin n → U)
    (hv : ∀ j, ActionCovered base A (v j)) :
    LocalActionTruth base J (.impl p q) A v ↔ (LocalActionTruth base J p A v → LocalActionTruth base J q A v) := by
  obtain ⟨B, f, E, hBJ, V, hV⟩ := covered_action_environment_realized base ctx A v hv
  rw [local_action_truth_realization_iff base ctx E hBJ (.impl p q) v V hV,
    local_action_truth_realization_iff base ctx E hBJ p v V hV,
    local_action_truth_realization_iff base ctx E hBJ q v V hV]
  rfl

theorem local_action_truth_negation (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) {n} (p : Formula n) (v : Fin n → U)
    (hv : ∀ j, ActionCovered base A (v j)) :
    LocalActionTruth base J (.impl p .bottom) A v ↔ ¬LocalActionTruth base J p A v := by
  rw [local_action_truth_impl base ctx A p .bottom v hv]
  have hb := local_action_truth_bounded base ctx A BoundedFormula.bottom v hv
  exact imp_congr Iff.rfl hb

theorem local_action_truth_all_dual (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) {n} (p : Formula (n+1)) (v : Fin n → U)
    (hv : ∀ j, ActionCovered base A (v j)) :
    LocalActionTruth base J (.all p) A v ↔ ¬LocalActionTruth base J (.ex (.impl p .bottom)) A v := by
  classical
  obtain ⟨B, f, E, hBJ, V, hV⟩ := covered_action_environment_realized base ctx A v hv
  rw [local_action_truth_realization_iff base ctx E hBJ (.all p) v V hV,
    local_action_truth_realization_iff base ctx E hBJ (.ex (.impl p .bottom)) v V hV]
  change (∀ x, Eval (coveredMaskMember J) p (cons x V)) ↔ ¬∃ x, ¬Eval (coveredMaskMember J) p (cons x V)
  constructor
  · intro h ⟨x, hx⟩
    exact hx (h x)
  · intro h x
    exact Classical.byContradiction (fun hx => h ⟨x, hx⟩)

#print axioms local_action_truth_all_dual
end FullBridge
