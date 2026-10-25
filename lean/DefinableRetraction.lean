import TheoryRetraction
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def selfSingletonAtFormula {n} (i : Fin n) : Formula n :=
  .all ((Formula.member 0 i.succ).iffF (.equal 0 i.succ))

theorem eval_selfSingletonAtFormula {n} (i : Fin n) (v : Fin n → U) :
    Eval s (selfSingletonAtFormula i) v ↔ SelfSingleton s (v i) := by
  simp only [selfSingletonAtFormula, Eval, eval_iffF, cons_zero, cons_succ, SelfSingleton]

/-- Bind the parameter of a relation with context [value,node,parameter]. -/
def bindSelfSingleton (p : Formula 3) : Formula 2 :=
  .ex (.conj (selfSingletonAtFormula 0)
    (p.rename (Fin.cases 1 (Fin.cases 2 (Fin.cases 0 Fin.elim0)))))

theorem eval_bindSelfSingleton (p : Formula 3) (x z : U) :
    Eval s (bindSelfSingleton p) (cons z (cons x Fin.elim0)) ↔
      ∃ b, SelfSingleton s b ∧ Eval s p (cons z (cons x (cons b Fin.elim0))) := by
  simp only [bindSelfSingleton, Eval, eval_selfSingletonAtFormula, eval_rename, cons_zero]
  apply exists_congr
  intro b
  apply and_congr_right
  intro _
  have he : (fun i => (cons b (cons z (cons x Fin.elim0)))
      (Fin.cases 1 (Fin.cases 2 (Fin.cases 0 Fin.elim0)) i)) =
      cons z (cons x (cons b Fin.elim0)) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
  rw [he]

/-- Free variables [value, representative]; no external set parameter. -/
def recoveryFormula : Formula 2 :=
  bindSelfSingleton (globalDecorationFormula prunedMemberFormula)

theorem eval_recoveryFormula (x z : U) :
    Eval s recoveryFormula (cons z (cons x Fin.elim0)) ↔
      ∃ b, SelfSingleton s b ∧ DefinedDecorationValue s prunedMemberFormula (cons b Fin.elim0) x z := by
  exact (eval_bindSelfSingleton (globalDecorationFormula prunedMemberFormula) x z).trans
    (exists_congr (fun b => and_congr_right (fun _ =>
      eval_globalDecorationFormula prunedMemberFormula (cons b Fin.elim0) x z)))

theorem recovery_formula_value (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hb : SelfSingleton s b) (x z : U) :
    Eval s recoveryFormula (cons z (cons x Fin.elim0)) ↔
      prunedEvaluationMap base hA b (prunedCode base b x) = z := by
  rw [eval_recoveryFormula]
  constructor
  · rintro ⟨c, hc, hval⟩
    have hcb := afa_selfSingleton_unique base hA hc hb
    subst c
    exact (canonical_graph_value_iff base hA prunedMemberFormula (cons b Fin.elim0)
      (pruned_edges_are_members b) x z).mp hval
  · intro h
    exact ⟨b, hb, (canonical_graph_value_iff base hA prunedMemberFormula (cons b Fin.elim0)
      (pruned_edges_are_members b) x z).mpr h⟩

theorem recovery_formula_total_unique (base : BaseCollection s) (hA : AFACode s) (x : U) :
    ∃ z, Eval s recoveryFormula (cons z (cons x Fin.elim0)) ∧
      ∀ w, Eval s recoveryFormula (cons w (cons x Fin.elim0)) → w = z := by
  obtain ⟨b, hb⟩ := solvability_selfSingleton_exists base (afa_graph_solvability hA)
  refine ⟨_, (recovery_formula_value base hA hb x _).mpr rfl, ?_⟩
  intro w hw
  exact ((recovery_formula_value base hA hb x w).mp hw).symm

theorem recovery_formula_surjective (base : BaseCollection s) (hA : AFACode s) (z : U) :
    ∃ x, Eval s recoveryFormula (cons z (cons x Fin.elim0)) := by
  obtain ⟨b, hb⟩ := solvability_selfSingleton_exists base (afa_graph_solvability hA)
  obtain ⟨X, hX⟩ := pruned_evaluation_surjective base hA hb z
  obtain ⟨x, _, rfl⟩ := pruned_good_representative base b X
  exact ⟨x, (recovery_formula_value base hA hb x z).mpr hX⟩

theorem recovery_formula_function_on_set (base : BaseCollection s) (hA : AFACode s) (a : U) :
    ∃ f, FunctionCode s a f ∧ ∀ x z, CodedRelation s f x z ↔
      s x a ∧ Eval s recoveryFormula (cons z (cons x Fin.elim0)) := by
  obtain ⟨b, hb⟩ := solvability_selfSingleton_exists base (afa_graph_solvability hA)
  obtain ⟨f, hf, hfr⟩ := canonical_graph_value_function base hA prunedMemberFormula
    (cons b Fin.elim0) (pruned_edges_are_members b) a
  exact ⟨f, hf, fun x z => (hfr x z).trans
    (and_congr_right (fun _ => (recovery_formula_value base hA hb x z).symm))⟩

/-- Uniform composite interpretation, with the source quine existentially bound.
    This operation preserves the number of free variables. -/
def recoveryTranslation {n} (p : Formula n) : Formula n :=
  .ex (.conj (selfSingletonAtFormula 0) (prunedTheoryTranslation (behaviorTranslation p)))

theorem parameterized_recovery_translation (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hb : SelfSingleton s b) {n} (p : Formula n) (v : Fin n → U) :
    Eval s (prunedTheoryTranslation (behaviorTranslation p)) (cons b v) ↔
      Eval s p (fun i => prunedEvaluationMap base hA b (prunedCode base b (v i))) := by
  have hp := pruned_theory_formula_translation base b (behaviorTranslation p) v
  have hq := uniform_behavior_translation (pruned_quotient_base base ((hb b).mpr rfl)) p
    (fun i => prunedCode base b (v i))
  have hr := pruned_roundtrip_formula_semantics base hA hb p
    (fun i => internalCode (pruned_quotient_base base ((hb b).mpr rfl)) (prunedCode base b (v i)))
  exact hp.trans (hq.trans hr)

theorem recovery_translation_formula_semantics (base : BaseCollection s) (hA : AFACode s)
    {n} (p : Formula n) (v w : Fin n → U)
    (hvw : ∀ i, Eval s recoveryFormula (cons (w i) (cons (v i) Fin.elim0))) :
    Eval s (recoveryTranslation p) v ↔ Eval s p w := by
  obtain ⟨b, hb⟩ := solvability_selfSingleton_exists base (afa_graph_solvability hA)
  have henv : (fun i => prunedEvaluationMap base hA b (prunedCode base b (v i))) = w :=
    funext (fun i => (recovery_formula_value base hA hb (v i) (w i)).mp (hvw i))
  change (∃ c, Eval s (selfSingletonAtFormula 0) (cons c v) ∧
    Eval s (prunedTheoryTranslation (behaviorTranslation p)) (cons c v)) ↔ _
  simp only [eval_selfSingletonAtFormula, cons_zero]
  constructor
  · rintro ⟨c, hc, hp⟩
    have hcb := afa_selfSingleton_unique base hA hc hb
    subst c
    exact henv ▸ (parameterized_recovery_translation base hA hb p v).mp hp
  · intro hp
    exact ⟨b, hb, (parameterized_recovery_translation base hA hb p v).mpr (henv.symm ▸ hp)⟩

theorem recovery_translation_equal (base : BaseCollection s) (hA : AFACode s)
    {x y z w : U}
    (hx : Eval s recoveryFormula (cons z (cons x Fin.elim0)))
    (hy : Eval s recoveryFormula (cons w (cons y Fin.elim0))) :
    Eval s (recoveryTranslation (Formula.equal (n := 2) 0 1)) (pairEnv x y) ↔ z = w := by
  apply recovery_translation_formula_semantics base hA _ (pairEnv x y) (pairEnv z w)
  intro i
  exact Fin.cases hx (fun j => Fin.cases hy (fun k => Fin.elim0 k) j) i

theorem recovery_translation_member (base : BaseCollection s) (hA : AFACode s)
    {x y z w : U}
    (hx : Eval s recoveryFormula (cons z (cons x Fin.elim0)))
    (hy : Eval s recoveryFormula (cons w (cons y Fin.elim0))) :
    Eval s (recoveryTranslation (Formula.member (n := 2) 0 1)) (pairEnv x y) ↔ s z w := by
  apply recovery_translation_formula_semantics base hA _ (pairEnv x y) (pairEnv z w)
  intro i
  exact Fin.cases hx (fun j => Fin.cases hy (fun k => Fin.elim0 k) j) i

theorem recovery_translation_sentence (base : BaseCollection s) (hA : AFACode s)
    (p : Formula 0) : Eval s (recoveryTranslation p) Fin.elim0 ↔ Eval s p Fin.elim0 :=
  recovery_translation_formula_semantics base hA p Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i)

#print axioms recovery_formula_function_on_set
#print axioms recovery_translation_formula_semantics
end FullBridge
