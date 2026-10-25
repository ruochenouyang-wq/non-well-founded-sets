import Schemes

namespace FullBridge
universe u v

def pairEnv {U : Type u} (x y : U) : Fin 2 → U := cons x (cons y Fin.elim0)

def atomRename {n} (i j : Fin n) : Fin 2 → Fin n :=
  Fin.cases i (Fin.cases j Fin.elim0)

def Formula.translate (eqF memF : Formula 2) : {n : Nat} → Formula n → Formula n
  | _, .equal i j => eqF.rename (atomRename i j)
  | _, .member i j => memF.rename (atomRename i j)
  | _, .bottom => .bottom
  | _, .conj p q => .conj (Formula.translate eqF memF p) (Formula.translate eqF memF q)
  | _, .impl p q => .impl (Formula.translate eqF memF p) (Formula.translate eqF memF q)
  | _, .ex p => .ex (Formula.translate eqF memF p)
  | _, .all p => .all (Formula.translate eqF memF p)

theorem atom_env {U : Type u} {n} (i j : Fin n) (e : Fin n → U) :
    (fun k => e (atomRename i j k)) = pairEnv (e i) (e j) := by
  funext k
  exact Fin.cases rfl (fun l => Fin.cases rfl (fun z => Fin.elim0 z) l) k

theorem cons_map {U : Type u} {V : Type v} {n} (q : U → V) (x : U) (e : Fin n → U) :
    (fun i => q (cons x e i)) = cons (q x) (fun i => q (e i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/- These are explicit interpretation obligations, not claims that BAFA supplies them. -/
structure AtomicInterpretation {U : Type u} {V : Type v}
    (s : U → U → Prop) (t : V → V → Prop) (q : U → V) where
  equalFormula : Formula 2
  memberFormula : Formula 2
  equal_correct : ∀ x y, Eval s equalFormula (pairEnv x y) ↔ q x = q y
  member_correct : ∀ x y, Eval s memberFormula (pairEnv x y) ↔ t (q x) (q y)

theorem eval_translate {U : Type u} {V : Type v}
    {s : U → U → Prop} {t : V → V → Prop} {q : U → V}
    (I : AtomicInterpretation s t q) (onto : ∀ y, ∃ x, q x = y)
    {n} (p : Formula n) (e : Fin n → U) :
    Eval s (Formula.translate I.equalFormula I.memberFormula p) e ↔
      Eval t p (fun i => q (e i)) := by
  induction p with
  | equal i j =>
    simpa only [Formula.translate, Eval, eval_rename, atom_env] using I.equal_correct (e i) (e j)
  | member i j =>
    simpa only [Formula.translate, Eval, eval_rename, atom_env] using I.member_correct (e i) (e j)
  | bottom => rfl
  | conj p r hp hr => simp only [Formula.translate, Eval, hp, hr]
  | impl p r hp hr => simp only [Formula.translate, Eval, hp, hr]
  | ex p hp =>
    change (∃ x, Eval s (Formula.translate I.equalFormula I.memberFormula p) (cons x e)) ↔ _
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨q x, ?_⟩
      simpa only [cons_map] using (hp (cons x e)).mp hx
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := onto y
      refine ⟨x, (hp (cons x e)).mpr ?_⟩
      simpa only [cons_map] using hy
  | all p hp =>
    change (∀ x, Eval s (Formula.translate I.equalFormula I.memberFormula p) (cons x e)) ↔ _
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := onto y
      simpa only [cons_map] using (hp (cons x e)).mp (h x)
    · intro h x
      apply (hp (cons x e)).mpr
      simpa only [cons_map] using h (q x)

#print axioms eval_translate
end FullBridge
