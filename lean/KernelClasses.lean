import ChoiceAxiom
namespace FullBridge
universe u v
variable {U : Type u} {V : Type v} {s : U → U → Prop} {q : U → V}

def KernelClass (s : U → U → Prop) (q : U → V) (a x c : U) : Prop :=
  ∀ z, s z c ↔ s z a ∧ q z = q x

def kernelClassFormula (eqF : Formula 2) {n} (c x a : Fin n) : Formula n :=
  .all ((Formula.member 0 c.succ).iffF
    (.conj (.member 0 a.succ) (eqF.rename (atomRename 0 x.succ))))

theorem eval_kernelClassFormula (eqF : Formula 2)
    (heq : ∀ x y, Eval s eqF (pairEnv x y) ↔ q x = q y)
    {n} (c x a : Fin n) (v : Fin n → U) :
    Eval s (kernelClassFormula eqF c x a) v ↔ KernelClass s q (v a) (v x) (v c) := by
  simp only [kernelClassFormula, Eval, eval_iffF, eval_rename, atom_env, heq, cons_succ]
  rfl

theorem kernel_class_exists (base : BaseCollection s) (eqF : Formula 2)
    (heq : ∀ x y, Eval s eqF (pairEnv x y) ↔ q x = q y) (a x : U) :
    ∃ c, KernelClass s q a x c := by
  obtain ⟨c, hc⟩ := base.separation 1 eqF (cons x Fin.elim0) a
  refine ⟨c, ?_⟩
  intro z
  have h := hc z
  change s z c ↔ s z a ∧ Eval s eqF (pairEnv z x) at h
  rw [heq] at h
  exact h

theorem kernel_class_eq (hext : Extensional s) {a x y c d : U}
    (hc : KernelClass s q a x c) (hd : KernelClass s q a y d)
    (hxy : q x = q y) : c = d := by
  apply hext
  intro z
  rw [hc z, hd z, hxy]

def kernelClassFamilyFormula (eqF : Formula 2) : Formula 2 :=
  .ex (.conj (.member 0 2) (kernelClassFormula eqF 1 0 2))

theorem eval_kernelClassFamilyFormula (eqF : Formula 2)
    (heq : ∀ x y, Eval s eqF (pairEnv x y) ↔ q x = q y) (c a : U) :
    Eval s (kernelClassFamilyFormula eqF) (cons c (cons a Fin.elim0)) ↔
      ∃ x, s x a ∧ KernelClass s q a x c := by
  simp only [kernelClassFamilyFormula, Eval, eval_kernelClassFormula eqF heq]
  rfl

theorem kernel_class_family (base : BaseCollection s) (eqF : Formula 2)
    (heq : ∀ x y, Eval s eqF (pairEnv x y) ↔ q x = q y) (a : U) :
    ∃ b, ∀ c, s c b ↔ ∃ x, s x a ∧ KernelClass s q a x c := by
  obtain ⟨pa, hpa⟩ := base.powerset a
  obtain ⟨b, hb⟩ := base.separation 1 (kernelClassFamilyFormula eqF) (cons a Fin.elim0) pa
  refine ⟨b, ?_⟩
  intro c
  have h := hb c
  rw [eval_kernelClassFamilyFormula eqF heq] at h
  constructor
  · intro hc
    exact (h.mp hc).2
  · rintro ⟨x, hx, hc⟩
    exact h.mpr ⟨(hpa c).mpr (fun z hz => ((hc z).mp hz).1), x, hx, hc⟩

#print axioms kernel_class_family
end FullBridge
