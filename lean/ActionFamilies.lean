import LocalWitnessPackages
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A source set of triple codes, each carrying a distinguished point,
    a domain and the entire action family. The point need not be in the domain. -/
def ActionFamilyMember (base : BaseCollection s) {w : U}
    (p : U) (Q : CodedMaskAction base w) : Prop :=
  ∃ y, OrbitGraphParameters s p y Q.domain Q.family

def ActionFamilyCode (base : BaseCollection s) (w O : U) : Prop :=
  ∀ p, s p O → ∃ Q : CodedMaskAction base w, ActionFamilyMember base p Q

theorem action_family_member_unique (base : BaseCollection s) {w p : U}
    {Q R : CodedMaskAction base w} (hQ : ActionFamilyMember base p Q)
    (hR : ActionFamilyMember base p R) : Q = R := by
  obtain ⟨y, hy⟩ := hQ
  obtain ⟨z, hz⟩ := hR
  have h := orbit_graph_parameters_unique hy hz
  exact coded_mask_action_ext base Q R h.2.1 h.2.2

/-- Select a record from the actual code; uniqueness prevents an extra
    independent choice of action maps from entering the family construction. -/
noncomputable def familyAction (base : BaseCollection s) {w O : U}
    (h : ActionFamilyCode base w O) (p : {p // s p O}) : CodedMaskAction base w :=
  Classical.choose (h p.val p.property)

theorem family_action_member (base : BaseCollection s) {w O : U}
    (h : ActionFamilyCode base w O) (p : {p // s p O}) :
    ActionFamilyMember base p.val (familyAction base h p) :=
  Classical.choose_spec (h p.val p.property)

def witnessFamilyRename {n} : Fin (n+6) → Fin (n+7) :=
  Fin.cases 1 (Fin.cases 0 (Fin.cases 2 (Fin.cases 3 (Fin.cases 4
    (Fin.cases 5 (fun i => i.succ.succ.succ.succ.succ.succ.succ))))))

def witnessFamilyFilterFormula {n} (p : BoundedFormula (n+2)) : Formula (n+6) :=
  .ex (.conj (.member 0 6) ((localWitnessPackageFormula p).rename witnessFamilyRename))

theorem eval_witnessFamilyFilterFormula {n} (p : BoundedFormula (n+2))
    (P w D G K a : U) (v : Fin n → U) :
    Eval s (witnessFamilyFilterFormula p) (cons P (cons w (cons D (cons G (cons K (cons a v)))))) ↔
      ∃ x, s x a ∧ Eval s (localWitnessPackageFormula p)
        (cons P (cons x (cons w (cons D (cons G (cons K v)))))) := by
  simp only [witnessFamilyFilterFormula, Eval, eval_rename]
  have he : ∀ x, (fun i => cons x (cons P (cons w (cons D (cons G (cons K (cons a v))))))
      (witnessFamilyRename i)) = cons P (cons x (cons w (cons D (cons G (cons K v))))) := by
    intro x
    funext i
    refine Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl
      (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl
        (fun _ => rfl) j) j) j) j) j) i
  simp only [he]
  rfl

/-- Remove extraneous elements of the Collection bound by an actual source
    formula, so every remaining label carries a compatible action. -/
theorem local_witness_action_family (base : BaseCollection s) {w : U}
    (A : CodedMaskAction base w) {n} (p : BoundedFormula (n+2)) (v : Fin n → U) (a : U)
    (ht : ∀ x, s x a → ∃ Q : CodedMaskAction base w, CodedMaskExtends base A Q ∧
      ∃ y, ActionCovered base Q y ∧ BoundedEval s p (cons y (cons x v))) :
    ∃ O, ActionFamilyCode base w O ∧
      (∀ P Q, s P O → ActionFamilyMember base P Q → CodedMaskExtends base A Q) ∧
      ∀ x, s x a → ∃ P, s P O ∧ ∃ Q : CodedMaskAction base w, ∃ y,
        OrbitGraphParameters s P y Q.domain Q.family ∧ CodedMaskExtends base A Q ∧
          ActionCovered base Q y ∧ BoundedEval s p (cons y (cons x v)) := by
  obtain ⟨B, hB⟩ := local_witness_package_collection base A p v a ht
  obtain ⟨O, hO⟩ := base.separation (n+5) (witnessFamilyFilterFormula p)
    (cons w (cons A.domain (cons A.masks (cons A.family (cons a v))))) B
  have hm : ∀ P, s P O ↔ s P B ∧ ∃ x, s x a ∧ Eval s (localWitnessPackageFormula p)
      (cons P (cons x (cons w (cons A.domain (cons A.masks (cons A.family v)))))) := by
    intro P
    exact (hO P).trans (and_congr Iff.rfl (eval_witnessFamilyFilterFormula p P w A.domain A.masks A.family a v))
  refine ⟨O, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨_, x, _, hh⟩ := (hm P).mp hP
    obtain ⟨Q, y, hy, _⟩ := (local_witness_package_iff_record base A p P x v).mp hh
    exact ⟨Q, y, hy⟩
  · intro P Q hP hQ
    obtain ⟨_, x, _, hh⟩ := (hm P).mp hP
    obtain ⟨R, y, hy, he, _⟩ := (local_witness_package_iff_record base A p P x v).mp hh
    exact (action_family_member_unique base ⟨y, hy⟩ hQ) ▸ he
  · intro x hx
    obtain ⟨P, hPB, Q, y, hy, he, hc, hp⟩ := hB x hx
    exact ⟨P, (hm P).mpr ⟨hPB, x, hx,
      (local_witness_package_iff_record base A p P x v).mpr ⟨Q, y, hy, he, hc, hp⟩⟩,
      Q, y, hy, he, hc, hp⟩

#print axioms local_witness_action_family
end FullBridge
