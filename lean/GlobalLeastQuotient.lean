import DefinableClosedCover
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

def leastGlobalSetoid (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x) : Setoid U where
  r := DefinedLeastRelation s p v
  iseqv := defined_least_equivalence base p v hmem

abbrev LeastGlobalQuotient (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x) :=
  Quotient (leastGlobalSetoid base p v hmem)

def leastGlobalCode (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x)
    (x : U) : LeastGlobalQuotient base p v hmem := Quotient.mk _ x

def leastGlobalMember (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x)
    (x a : LeastGlobalQuotient base p v hmem) : Prop :=
  ∃ y b, leastGlobalCode base p v hmem y = x ∧
    leastGlobalCode base p v hmem b = a ∧ FormulaEdges s p v b y

theorem least_global_code_eq (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x) (x y : U) :
    leastGlobalCode base p v hmem x = leastGlobalCode base p v hmem y ↔
      DefinedLeastRelation s p v x y :=
  ⟨Quotient.exact, fun h => @Quotient.sound U (leastGlobalSetoid base p v hmem) x y h⟩

theorem least_global_code_onto (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x) :
    ∀ y, ∃ x, leastGlobalCode base p v hmem x = y := by
  intro y
  exact Quotient.inductionOn y (fun x => ⟨x, rfl⟩)

/-- Exact rows concern graph edges, not all source membership edges. -/
theorem least_global_exact_members (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x) :
    ExactMembers (fun y x => FormulaEdges s p v x y)
      (leastGlobalMember base p v hmem) (leastGlobalCode base p v hmem) := by
  intro a y
  constructor
  · rintro ⟨x, b, hxy, hba, hbx⟩
    have hR := (least_global_code_eq base p v hmem b a).mp hba
    obtain ⟨z, haz, hxz⟩ := ((defined_least_fixed base p v hmem b a).mp hR).1 x hbx
    exact ⟨z, haz, ((least_global_code_eq base p v hmem x z).mpr hxz).symm.trans hxy⟩
  · rintro ⟨x, hax, hxy⟩
    exact ⟨x, a, hxy, rfl, hax⟩

theorem least_global_extensional (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x) :
    Extensional (leastGlobalMember base p v hmem) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y h
  apply (least_global_code_eq base p v hmem x y).mpr
  apply (defined_least_fixed base p v hmem x y).mpr
  constructor
  · intro z hxz
    have hz := (least_global_exact_members base p v hmem x _).mpr ⟨z, hxz, rfl⟩
    obtain ⟨w, hyw, hwz⟩ := (least_global_exact_members base p v hmem y _).mp ((h _).mp hz)
    exact ⟨w, hyw, (least_global_code_eq base p v hmem z w).mp hwz.symm⟩
  · intro w hyw
    have hw := (least_global_exact_members base p v hmem y _).mpr ⟨w, hyw, rfl⟩
    obtain ⟨z, hxz, hzw⟩ := (least_global_exact_members base p v hmem x _).mp ((h _).mpr hw)
    exact ⟨z, hxz, (least_global_code_eq base p v hmem z w).mp hzw⟩

/-- Atom contexts are [first argument, second argument, fixed parameters]. -/
def parameterAtomRename {k m} (i j : Fin m) (w : Fin k → Fin m) : Fin (k + 2) → Fin m :=
  cons i (cons j w)

theorem parameter_atom_env {k m} (i j : Fin m) (w : Fin k → Fin m) (e : Fin m → U) :
    (fun l => e (parameterAtomRename i j w l)) = cons (e i) (cons (e j) (fun l => e (w l))) := by
  funext l
  exact Fin.cases rfl (fun l => Fin.cases rfl (fun _ => rfl) l) l

/-- Parameters remain fixed while quantifiers range over every source object. -/
def Formula.translateParameters {k} (eqF memF : Formula (k + 2)) :
    {n m : Nat} → (Fin k → Fin m) → (Fin n → Fin m) → Formula n → Formula m
  | _, _, w, f, .equal i j => eqF.rename (parameterAtomRename (f i) (f j) w)
  | _, _, w, f, .member i j => memF.rename (parameterAtomRename (f i) (f j) w)
  | _, _, _, _, .bottom => .bottom
  | _, _, w, f, .conj p q => .conj (Formula.translateParameters eqF memF w f p) (Formula.translateParameters eqF memF w f q)
  | _, _, w, f, .impl p q => .impl (Formula.translateParameters eqF memF w f p) (Formula.translateParameters eqF memF w f q)
  | _, _, w, f, .ex p => .ex (Formula.translateParameters eqF memF (fun j => (w j).succ) (liftRename f) p)
  | _, _, w, f, .all p => .all (Formula.translateParameters eqF memF (fun j => (w j).succ) (liftRename f) p)

theorem parameter_quantifier_env {V : Type v} (q : U → V) {n m}
    (f : Fin n → Fin m) (e : Fin m → U) (x : U) :
    (fun i => q (cons x e (liftRename f i))) = cons (q x) (fun i => q (e (f i))) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem eval_translate_parameters {V : Type v} {t : V → V → Prop} (q : U → V)
    {k} (eqF memF : Formula (k + 2)) (params : Fin k → U)
    (heq : ∀ x y, Eval s eqF (cons x (cons y params)) ↔ q x = q y)
    (hmem : ∀ x y, Eval s memF (cons x (cons y params)) ↔ t (q x) (q y))
    (onto : ∀ y, ∃ x, q x = y) {n m} (p : Formula n)
    (w : Fin k → Fin m) (f : Fin n → Fin m) (e : Fin m → U)
    (hp : ∀ j, e (w j) = params j) :
    Eval s (Formula.translateParameters eqF memF w f p) e ↔ Eval t p (fun i => q (e (f i))) := by
  induction p generalizing m with
  | equal i j =>
    simpa only [Formula.translateParameters, eval_rename, parameter_atom_env, hp, Eval] using heq (e (f i)) (e (f j))
  | member i j =>
    simpa only [Formula.translateParameters, eval_rename, parameter_atom_env, hp, Eval] using hmem (e (f i)) (e (f j))
  | bottom => rfl
  | conj p r ihp ihr => simp only [Formula.translateParameters, Eval, ihp w f e hp, ihr w f e hp]
  | impl p r ihp ihr => simp only [Formula.translateParameters, Eval, ihp w f e hp, ihr w f e hp]
  | ex p ih =>
    change (∃ x, Eval s (Formula.translateParameters eqF memF _ _ p) (cons x e)) ↔ _
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨q x, ?_⟩
      have hi := (ih (fun j => (w j).succ) (liftRename f) (cons x e) hp).mp hx
      simpa only [parameter_quantifier_env] using hi
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := onto y
      refine ⟨x, (ih (fun j => (w j).succ) (liftRename f) (cons x e) hp).mpr ?_⟩
      simpa only [parameter_quantifier_env] using hy
  | all p ih =>
    change (∀ x, Eval s (Formula.translateParameters eqF memF _ _ p) (cons x e)) ↔ _
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := onto y
      have hi := (ih (fun j => (w j).succ) (liftRename f) (cons x e) hp).mp (h x)
      simpa only [parameter_quantifier_env] using hi
    · intro h x
      apply (ih (fun j => (w j).succ) (liftRename f) (cons x e) hp).mpr
      simpa only [parameter_quantifier_env] using h (q x)

def leastGlobalEqualFormula {n} (p : Formula (n + 2)) : Formula (n + 2) :=
  (globalLeastFormula p).rename (cons 1 (cons 0 (fun j => j.succ.succ)))

theorem eval_leastGlobalEqualFormula {n} (p : Formula (n + 2)) (params : Fin n → U) (x y : U) :
    Eval s (leastGlobalEqualFormula p) (cons x (cons y params)) ↔ DefinedLeastRelation s p params x y := by
  rw [leastGlobalEqualFormula, eval_rename]
  have he : (fun i => cons x (cons y params) (cons 1 (cons 0 (fun j => j.succ.succ)) i)) = cons y (cons x params) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
  rw [he]
  exact eval_globalLeastFormula p params x y

def leastGlobalMemberFormula {n} (p : Formula (n + 2)) : Formula (n + 2) :=
  .ex (.conj (p.rename (cons 0 (cons 2 (fun j => j.succ.succ.succ))))
    ((globalLeastFormula p).rename (cons 1 (cons 0 (fun j => j.succ.succ.succ)))))

theorem eval_leastGlobalMemberFormula (base : BaseCollection s) {n} (p : Formula (n + 2))
    (params : Fin n → U) (hmem : ∀ x y, FormulaEdges s p params x y → s y x) (x a : U) :
    Eval s (leastGlobalMemberFormula p) (cons x (cons a params)) ↔
      leastGlobalMember base p params hmem (leastGlobalCode base p params hmem x)
        (leastGlobalCode base p params hmem a) := by
  have hedge (z : U) : (fun i => cons z (cons x (cons a params)) (cons 0 (cons 2 (fun j => j.succ.succ.succ)) i)) = cons z (cons a params) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
  have hrel (z : U) : (fun i => cons z (cons x (cons a params)) (cons 1 (cons 0 (fun j => j.succ.succ.succ)) i)) = cons x (cons z params) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
  simp only [leastGlobalMemberFormula, Eval, eval_rename, hedge, hrel, eval_globalLeastFormula]
  change (∃ z, FormulaEdges s p params a z ∧ DefinedLeastRelation s p params z x) ↔ _
  simp only [← least_global_code_eq base p params hmem]
  exact (least_global_exact_members base p params hmem a _).symm

theorem least_global_formula_translation (base : BaseCollection s) {k n m}
    (p : Formula (k + 2)) (params : Fin k → U)
    (hmem : ∀ x y, FormulaEdges s p params x y → s y x)
    (r : Formula n) (w : Fin k → Fin m) (f : Fin n → Fin m) (e : Fin m → U)
    (hp : ∀ j, e (w j) = params j) :
    Eval s (Formula.translateParameters (leastGlobalEqualFormula p) (leastGlobalMemberFormula p) w f r) e ↔
      Eval (leastGlobalMember base p params hmem) r (fun i => leastGlobalCode base p params hmem (e (f i))) := by
  apply eval_translate_parameters _ _ _ params _ _ (least_global_code_onto base p params hmem) r w f e hp
  · intro x y
    exact (eval_leastGlobalEqualFormula p params x y).trans (least_global_code_eq base p params hmem x y).symm
  · exact eval_leastGlobalMemberFormula base p params hmem

#print axioms least_global_extensional
#print axioms least_global_formula_translation
end FullBridge
