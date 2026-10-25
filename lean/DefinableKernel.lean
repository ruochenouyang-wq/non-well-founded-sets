import WellFoundedParameters

namespace FullBridge
universe u v

def memberFromKernel (eqF : Formula 2) : Formula 2 :=
  .ex (.conj (.member 0 2) (eqF.rename (atomRename 0 1)))

theorem eval_memberFromKernel {U : Type u} {V : Type v}
    {s : U → U → Prop} {t : V → V → Prop} {q : U → V}
    (eqF : Formula 2)
    (heq : ∀ x y, Eval s eqF (pairEnv x y) ↔ q x = q y)
    (hm : ExactMembers s t q) (x a : U) :
    Eval s (memberFromKernel eqF) (pairEnv x a) ↔ t (q x) (q a) := by
  change (∃ z, s z a ∧ Eval s (eqF.rename (atomRename 0 1)) (cons z (pairEnv x a))) ↔ _
  simp only [eval_rename, atom_env]
  change (∃ z, s z a ∧ Eval s eqF (pairEnv z x)) ↔ _
  simp only [heq]
  exact (hm a (q x)).symm

def interpretationFromKernel {U : Type u} {V : Type v}
    {s : U → U → Prop} {t : V → V → Prop} {q : U → V}
    (eqF : Formula 2)
    (heq : ∀ x y, Eval s eqF (pairEnv x y) ↔ q x = q y)
    (hm : ExactMembers s t q) : AtomicInterpretation s t q where
  equalFormula := eqF
  memberFormula := memberFromKernel eqF
  equal_correct := heq
  member_correct := eval_memberFromKernel eqF heq hm

theorem quotient_base_of_definable_behavior {U : Type u} (s : U → U → Prop)
    (eqF : Formula 2)
    (hdef : ∀ a b, Eval s eqF (pairEnv a b) ↔ Behavior s a b)
    (base : BaseCollection s) : BaseCollection (behaviorMember s) := by
  have hkernel : ∀ a b, Eval s eqF (pairEnv a b) ↔ behaviorCode s a = behaviorCode s b := by
    intro a b
    exact (hdef a b).trans (behavior_code_eq a b).symm
  exact behavior_base_transfer s
    (interpretationFromKernel eqF hkernel (behavior_exact_members s)) base

#print axioms quotient_base_of_definable_behavior
end FullBridge
