import UniversalFullSourceTruth
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def fullWitnessPackageRename {n} : Fin (n+6) → Fin (n+10) :=
  Fin.cases 6 (Fin.cases 3 (Fin.cases 2 (Fin.cases 1 (Fin.cases 0
    (Fin.cases 5 (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))))))

def fullWitnessPackageFormula {n} (p : Formula (n+2)) : Formula (n+6) :=
  .ex (.ex (.ex (.ex (.conj (orbitGraphParametersFormula 4 0 3 1)
    (.conj (rawMaskActionFormula 6 3 2 1) (.conj (rawActionExtendsFormula 8 7 9 3 1)
      (.conj (actionCoveredFormula 6 2 1 3 0) (p.actionTranslate.rename fullWitnessPackageRename))))))))

theorem eval_fullWitnessPackageFormula {n} (p : Formula (n+2))
    (P x w D G K : U) (v : Fin n → U) :
    Eval s (fullWitnessPackageFormula p) (cons P (cons x (cons w (cons D (cons G (cons K v)))))) ↔
      ∃ E H L y, OrbitGraphParameters s P y E L ∧ RawMaskAction s w E H L ∧
        RawActionExtends s G D K E L ∧ RawActionCovered s w H L E y ∧
          Eval s p.actionTranslate (cons w (cons E (cons H (cons L (cons y (cons x v)))))) := by
  simp only [fullWitnessPackageFormula, Eval, eval_orbitGraphParametersFormula,
    eval_rawMaskActionFormula, eval_rawActionExtendsFormula, eval_rawActionCoveredFormula, eval_rename]
  have he : ∀ E H L y,
      (fun i => cons y (cons L (cons H (cons E (cons P (cons x (cons w (cons D (cons G (cons K v)))))))))
        (fullWitnessPackageRename i)) = cons w (cons E (cons H (cons L (cons y (cons x v))))) := by
    intro E H L y
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl
      (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) j) j) j) j) i
  simp only [he]
  rfl

theorem full_witness_package_iff_record (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) {n} (p : Formula (n+2)) (P x : U) (v : Fin n → U)
    (hx : ActionCovered base A x) (hv : ∀ j, ActionCovered base A (v j)) :
    Eval s (fullWitnessPackageFormula p)
      (cons P (cons x (cons w (cons A.domain (cons A.masks (cons A.family v)))))) ↔
      ∃ Q : CodedMaskAction base w, ∃ y, OrbitGraphParameters s P y Q.domain Q.family ∧
        CodedMaskExtends base A Q ∧ ActionCovered base Q y ∧ LocalActionTruth base J p Q (cons y (cons x v)) := by
  rw [eval_fullWitnessPackageFormula]
  have hcovered : ∀ Q : CodedMaskAction base w, CodedMaskExtends base A Q → ∀ y, ActionCovered base Q y →
      ∀ j, ActionCovered base Q (cons y (cons x v) j) := by
    intro Q hAQ y hy j
    exact Fin.cases hy (fun j => Fin.cases (action_covered_extension base hAQ hx)
      (fun j => action_covered_extension base hAQ (hv j)) j) j
  constructor
  · rintro ⟨E, H, L, y, hP, hQ, he, hc, hp⟩
    obtain ⟨Q, rfl, rfl, rfl⟩ := raw_mask_action_record base hQ
    have hAQ := (raw_action_extends_iff base A Q).mp he
    have hy := (raw_action_covered_iff base Q).mp hc
    exact ⟨Q, y, hP, hAQ, hy, (eval_actionTranslate base ctx p Q (cons y (cons x v)) (hcovered Q hAQ y hy)).mp hp⟩
  · rintro ⟨Q, y, hP, he, hc, hp⟩
    exact ⟨Q.domain, Q.masks, Q.family, y, hP, coded_mask_action_raw base Q,
      (raw_action_extends_iff base A Q).mpr he, (raw_action_covered_iff base Q).mpr hc,
      (eval_actionTranslate base ctx p Q (cons y (cons x v)) (hcovered Q he y hc)).mpr hp⟩

def fullWitnessFamilyFilterFormula {n} (p : Formula (n+2)) : Formula (n+6) :=
  .ex (.conj (.member 0 6) ((fullWitnessPackageFormula p).rename witnessFamilyRename))

theorem eval_fullWitnessFamilyFilterFormula {n} (p : Formula (n+2))
    (P w D G K a : U) (v : Fin n → U) :
    Eval s (fullWitnessFamilyFilterFormula p) (cons P (cons w (cons D (cons G (cons K (cons a v)))))) ↔
      ∃ x, s x a ∧ Eval s (fullWitnessPackageFormula p)
        (cons P (cons x (cons w (cons D (cons G (cons K v)))))) := by
  simp only [fullWitnessFamilyFilterFormula, Eval, eval_rename]
  have he : ∀ x, (fun i => cons x (cons P (cons w (cons D (cons G (cons K (cons a v))))))
      (witnessFamilyRename i)) = cons P (cons x (cons w (cons D (cons G (cons K v))))) := by
    intro x
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl
      (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) j) j) j) j) i
  simp only [he]
  rfl

#print axioms full_witness_package_iff_record
end FullBridge
