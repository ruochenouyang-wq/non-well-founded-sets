import LocalActionTruthLogic
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def actionExtensionRename {n} : Fin (n+5) → Fin (n+8) :=
  Fin.cases 4 (Fin.cases 3 (Fin.cases 2 (Fin.cases 1 (Fin.cases 0
    (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ)))))

/-- Four actual source quantifiers: new domain, masks, function family, witness. -/
def actionExtensionFormula {n} (q : Formula (n+5)) : Formula (n+4) :=
  .ex (.ex (.ex (.ex (.conj (rawMaskActionFormula 4 3 2 1)
    (.conj (rawActionExtendsFormula 6 5 7 3 1)
      (.conj (actionCoveredFormula 4 2 1 3 0) (q.rename actionExtensionRename)))))))

theorem eval_actionExtensionFormula {n} (q : Formula (n+5))
    (w D G K : U) (v : Fin n → U) :
    Eval s (actionExtensionFormula q) (cons w (cons D (cons G (cons K v)))) ↔
      ∃ E H L y, RawMaskAction s w E H L ∧ RawActionExtends s G D K E L ∧
        RawActionCovered s w H L E y ∧ Eval s q (cons w (cons E (cons H (cons L (cons y v))))) := by
  simp only [actionExtensionFormula, Eval, eval_rawMaskActionFormula,
    eval_rawActionExtendsFormula, eval_rawActionCoveredFormula, eval_rename]
  have he : ∀ E H L y,
      (fun i => cons y (cons L (cons H (cons E (cons w (cons D (cons G (cons K v)))))))
        (actionExtensionRename i)) = cons w (cons E (cons H (cons L (cons y v)))) := by
    intro E H L y
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl
      (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) j) j) j) i
  simp only [he]
  rfl

theorem action_extension_source_iff_record (base : BaseCollection s) {w : U}
    (A : CodedMaskAction base w) {n} (q : Formula (n+5)) (v : Fin n → U) :
    Eval s (actionExtensionFormula q) (cons w (cons A.domain (cons A.masks (cons A.family v)))) ↔
      ∃ C : CodedMaskAction base w, CodedMaskExtends base A C ∧ ∃ y, ActionCovered base C y ∧
        Eval s q (cons w (cons C.domain (cons C.masks (cons C.family (cons y v))))) := by
  rw [eval_actionExtensionFormula]
  constructor
  · rintro ⟨D, G, K, y, hC, he, hc, hq⟩
    obtain ⟨C, rfl, rfl, rfl⟩ := raw_mask_action_record base hC
    exact ⟨C, (raw_action_extends_iff base A C).mp he, y, (raw_action_covered_iff base C).mp hc, hq⟩
  · rintro ⟨C, he, y, hc, hq⟩
    exact ⟨C.domain, C.masks, C.family, y, coded_mask_action_raw base C,
      (raw_action_extends_iff base A C).mpr he, (raw_action_covered_iff base C).mpr hc, hq⟩

/-- Recursive finite syntax; no J, Hc, action records or truth predicate
    occurs in the resulting object-language formula. -/
def Formula.actionTranslate : {n : Nat} → Formula n → Formula (n+4)
  | _, .equal i j => .equal i.succ.succ.succ.succ j.succ.succ.succ.succ
  | _, .member i j => .member i.succ.succ.succ.succ j.succ.succ.succ.succ
  | _, .bottom => .bottom
  | _, .conj p q => .conj p.actionTranslate q.actionTranslate
  | _, .impl p q => .impl p.actionTranslate q.actionTranslate
  | _, .ex p => actionExtensionFormula p.actionTranslate
  | _, .all p => .impl (actionExtensionFormula (.impl p.actionTranslate .bottom)) .bottom

theorem action_covered_extension (base : BaseCollection s) {w x : U}
    {A B : CodedMaskAction base w} (hAB : CodedMaskExtends base A B) (hx : ActionCovered base A x) :
    ActionCovered base B x :=
  coded_mask_embedding_cover_forward base (codedMaskExtensionEmbedding base hAB)
    ((coded_mask_one_graph base A x x).mpr ⟨action_covered_domain base hx, rfl⟩) hx

/-- Correctness of the complete recursive source translation for every finite
    formula, on locally covered parameters in the supplied action domain. -/
theorem eval_actionTranslate (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J) {n} (p : Formula n) :
    ∀ (A : CodedMaskAction base w) (v : Fin n → U), (∀ j, ActionCovered base A (v j)) →
      (Eval s p.actionTranslate (cons w (cons A.domain (cons A.masks (cons A.family v)))) ↔
        LocalActionTruth base J p A v) := by
  induction p with
  | equal i j =>
    intro A v hv
    exact (local_action_truth_bounded base ctx A (.equal i j) v hv).symm
  | member i j =>
    intro A v hv
    exact (local_action_truth_bounded base ctx A (.member i j) v hv).symm
  | bottom =>
    intro A v hv
    exact (local_action_truth_bounded base ctx A .bottom v hv).symm
  | conj p q hp hq =>
    intro A v hv
    exact (and_congr (hp A v hv) (hq A v hv)).trans (local_action_truth_conj base ctx A p q v hv).symm
  | impl p q hp hq =>
    intro A v hv
    exact (imp_congr (hp A v hv) (hq A v hv)).trans (local_action_truth_impl base ctx A p q v hv).symm
  | ex p ih =>
    intro A v hv
    change Eval s (actionExtensionFormula p.actionTranslate) _ ↔ _
    rw [action_extension_source_iff_record, local_action_truth_exists base ctx A p v (fun j => action_covered_domain base (hv j))]
    apply exists_congr
    intro C
    apply and_congr_right
    intro hAC
    apply exists_congr
    intro y
    apply and_congr_right
    intro hy
    exact ih C (cons y v) (fun j => Fin.cases hy (fun j => action_covered_extension base hAC (hv j)) j)
  | all p ih =>
    intro A v hv
    change (¬Eval s (actionExtensionFormula (.impl p.actionTranslate .bottom)) _) ↔ _
    rw [local_action_truth_all_dual base ctx A p v hv]
    apply not_congr
    rw [action_extension_source_iff_record, local_action_truth_exists base ctx A (.impl p .bottom) v
      (fun j => action_covered_domain base (hv j))]
    apply exists_congr
    intro C
    apply and_congr_right
    intro hAC
    apply exists_congr
    intro y
    apply and_congr_right
    intro hy
    have hc : ∀ j, ActionCovered base C (cons y v j) :=
      fun j => Fin.cases hy (fun j => action_covered_extension base hAC (hv j)) j
    exact (not_congr (ih C (cons y v) hc)).trans (local_action_truth_negation base ctx C p (cons y v) hc).symm

#print axioms eval_actionTranslate
end FullBridge
