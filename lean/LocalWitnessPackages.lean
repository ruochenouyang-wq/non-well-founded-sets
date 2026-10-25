import UniversalWitnessSource
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Witness and input go to positions 0 and 5; old parameters start at 10. -/
def witnessPackageRename {n} : Fin (n+2) → Fin (n+10) :=
  Fin.cases 0 (Fin.cases 5 (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))

/-- Free environment: package, input, w, old domain, masks, family, parameters. -/
def localWitnessPackageFormula {n} (p : BoundedFormula (n+2)) : Formula (n+6) :=
  .ex (.ex (.ex (.ex (.conj (orbitGraphParametersFormula 4 0 3 1)
    (.conj (rawMaskActionFormula 6 3 2 1) (.conj (rawActionExtendsFormula 8 7 9 3 1)
      (.conj (actionCoveredFormula 6 2 1 3 0) (p.toFormula.rename witnessPackageRename))))))))

theorem eval_localWitnessPackageFormula {n} (p : BoundedFormula (n+2))
    (P x w D G K : U) (v : Fin n → U) :
    Eval s (localWitnessPackageFormula p) (cons P (cons x (cons w (cons D (cons G (cons K v)))))) ↔
      ∃ E H L y, OrbitGraphParameters s P y E L ∧ RawMaskAction s w E H L ∧
        RawActionExtends s G D K E L ∧ RawActionCovered s w H L E y ∧
          BoundedEval s p (cons y (cons x v)) := by
  simp only [localWitnessPackageFormula, Eval, eval_orbitGraphParametersFormula,
    eval_rawMaskActionFormula, eval_rawActionExtendsFormula, eval_rawActionCoveredFormula, eval_rename]
  have he : ∀ E H L y,
      (fun i => cons y (cons L (cons H (cons E (cons P (cons x (cons w (cons D (cons G (cons K v)))))))))
        (witnessPackageRename i)) = cons y (cons x v) := by
    intro E H L y
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact Fin.cases rfl (fun _ => rfl) j
  simp only [he, bounded_eval_toFormula]
  rfl

theorem local_witness_package_iff_record (base : BaseCollection s) {w : U}
    (A : CodedMaskAction base w) {n} (p : BoundedFormula (n+2)) (P x : U) (v : Fin n → U) :
    Eval s (localWitnessPackageFormula p)
      (cons P (cons x (cons w (cons A.domain (cons A.masks (cons A.family v)))))) ↔
      ∃ Q : CodedMaskAction base w, ∃ y, OrbitGraphParameters s P y Q.domain Q.family ∧
        CodedMaskExtends base A Q ∧ ActionCovered base Q y ∧ BoundedEval s p (cons y (cons x v)) := by
  rw [eval_localWitnessPackageFormula]
  constructor
  · rintro ⟨E, H, L, y, hP, hQ, he, hc, hp⟩
    obtain ⟨Q, rfl, rfl, rfl⟩ := raw_mask_action_record base hQ
    exact ⟨Q, y, hP, (raw_action_extends_iff base A Q).mp he,
      (raw_action_covered_iff base Q).mp hc, hp⟩
  · rintro ⟨Q, y, hP, he, hc, hp⟩
    exact ⟨Q.domain, Q.masks, Q.family, y, hP, coded_mask_action_raw base Q,
      (raw_action_extends_iff base A Q).mpr he, (raw_action_covered_iff base Q).mpr hc, hp⟩

/-- Source Collection bounds actual packages containing local actions and witnesses.
    The images of these witnesses in Hc are not asserted to have a common bound. -/
theorem local_witness_package_collection (base : BaseCollection s) {w : U}
    (A : CodedMaskAction base w) {n} (p : BoundedFormula (n+2)) (v : Fin n → U) (a : U)
    (ht : ∀ x, s x a → ∃ Q : CodedMaskAction base w, CodedMaskExtends base A Q ∧
      ∃ y, ActionCovered base Q y ∧ BoundedEval s p (cons y (cons x v))) :
    ∃ B, ∀ x, s x a → ∃ P, s P B ∧ ∃ Q : CodedMaskAction base w, ∃ y,
      OrbitGraphParameters s P y Q.domain Q.family ∧ CodedMaskExtends base A Q ∧
        ActionCovered base Q y ∧ BoundedEval s p (cons y (cons x v)) := by
  obtain ⟨B, hB⟩ := base.collection (n+4) (localWitnessPackageFormula p)
    (cons w (cons A.domain (cons A.masks (cons A.family v)))) a (by
      intro x hx
      obtain ⟨Q, he, y, hc, hp⟩ := ht x hx
      obtain ⟨P, hP⟩ := orbit_graph_parameters_exists base y Q.domain Q.family
      exact ⟨P, (local_witness_package_iff_record base A p P x v).mpr ⟨Q, y, hP, he, hc, hp⟩⟩)
  refine ⟨B, fun x hx => ?_⟩
  obtain ⟨P, hPB, hP⟩ := hB x hx
  exact ⟨P, hPB, (local_witness_package_iff_record base A p P x v).mp hP⟩

/-- All selected source witnesses and action codes have one transitive source bound.
    This is a bound before embedding, not a bound on their images in Hc. -/
theorem local_witness_source_bound (base : BaseCollection s) {w : U}
    (A : CodedMaskAction base w) {n} (p : BoundedFormula (n+2)) (v : Fin n → U) (a : U)
    (ht : ∀ x, s x a → ∃ Q : CodedMaskAction base w, CodedMaskExtends base A Q ∧
      ∃ y, ActionCovered base Q y ∧ BoundedEval s p (cons y (cons x v))) :
    ∃ T, TransitiveCode s T ∧ ∀ x, s x a → ∃ Q : CodedMaskAction base w, ∃ y,
      s y T ∧ s Q.domain T ∧ s Q.family T ∧ CodedMaskExtends base A Q ∧
        ActionCovered base Q y ∧ BoundedEval s p (cons y (cons x v)) := by
  obtain ⟨B, hB⟩ := local_witness_package_collection base A p v a ht
  obtain ⟨T, hT, hBT⟩ := transitive_sets_cover base B
  refine ⟨T, hT, fun x hx => ?_⟩
  obtain ⟨P, hPB, Q, y, hP, he, hc, hp⟩ := hB x hx
  obtain ⟨hyT, hQT, hKT⟩ := orbit_graph_parameters_in_transitive hT (hT B hBT P hPB) hP
  exact ⟨Q, y, hyT, hQT, hKT, he, hc, hp⟩

#print axioms local_witness_source_bound
#print axioms local_witness_package_collection
end FullBridge
