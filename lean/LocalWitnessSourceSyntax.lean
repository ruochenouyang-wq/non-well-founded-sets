import RawActionExtensions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Free environment: w, old domain, old masks, old family, parameters.
    Bound environment: witness, new family, new masks, new domain, free environment. -/
def localWitnessRename {n} : Fin (n+1) → Fin (n+8) :=
  Fin.cases 0 (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ)

def boundedLocalWitnessFormula {n} (p : BoundedFormula (n+1)) : Formula (n+4) :=
  .ex (.ex (.ex (.ex (.conj (rawMaskActionFormula 4 3 2 1)
    (.conj (rawActionExtendsFormula 6 5 7 3 1)
      (.conj (actionCoveredFormula 4 2 1 3 0) (p.toFormula.rename localWitnessRename)))))))

def RawLocalWitness (s : U → U → Prop) {n} (p : BoundedFormula (n+1))
    (w D G K : U) (v : Fin n → U) : Prop :=
  ∃ E H L y, RawMaskAction s w E H L ∧ RawActionExtends s G D K E L ∧
    RawActionCovered s w H L E y ∧ BoundedEval s p (cons y v)

theorem eval_boundedLocalWitnessFormula {n} (p : BoundedFormula (n+1))
    (w D G K : U) (v : Fin n → U) :
    Eval s (boundedLocalWitnessFormula p) (cons w (cons D (cons G (cons K v)))) ↔
      RawLocalWitness s p w D G K v := by
  simp only [boundedLocalWitnessFormula, Eval, eval_rawMaskActionFormula,
    eval_rawActionExtendsFormula, eval_rawActionCoveredFormula, eval_rename]
  have he : ∀ E H L y,
      (fun i => cons y (cons L (cons H (cons E (cons w (cons D (cons G (cons K v)))))))
        (localWitnessRename i)) = cons y v := by
    intro E H L y
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  simp only [he, bounded_eval_toFormula]
  rfl

theorem bounded_local_source_iff_record (base : BaseCollection s) {w : U}
    (A : CodedMaskAction base w) {n} (p : BoundedFormula (n+1)) (v : Fin n → U) :
    Eval s (boundedLocalWitnessFormula p) (cons w (cons A.domain (cons A.masks (cons A.family v)))) ↔
      ∃ Q : CodedMaskAction base w, CodedMaskExtends base A Q ∧
        ∃ y, ActionCovered base Q y ∧ BoundedEval s p (cons y v) := by
  rw [eval_boundedLocalWitnessFormula]
  constructor
  · rintro ⟨E, H, L, y, hQ, he, hc, hp⟩
    obtain ⟨Q, rfl, rfl, rfl⟩ := raw_mask_action_record base hQ
    exact ⟨Q, (raw_action_extends_iff base A Q).mp he, y,
      (raw_action_covered_iff base Q).mp hc, hp⟩
  · rintro ⟨Q, he, y, hc, hp⟩
    exact ⟨Q.domain, Q.masks, Q.family, y, coded_mask_action_raw base Q,
      (raw_action_extends_iff base A Q).mpr he, (raw_action_covered_iff base Q).mpr hc, hp⟩

#print axioms bounded_local_source_iff_record
end FullBridge
