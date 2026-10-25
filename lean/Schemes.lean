import Syntax

namespace FullBridge
universe u
variable {U : Type u}

/- Schemes range over actual finite first-order formulas, not all external predicates. -/
def Separation (mem : U → U → Prop) : Prop :=
  ∀ n (p : Formula (n + 1)) (v : Fin n → U) (a : U),
    ∃ b, ∀ x, mem x b ↔ mem x a ∧ Eval mem p (cons x v)

def Collection (mem : U → U → Prop) : Prop :=
  ∀ n (p : Formula (n + 2)) (v : Fin n → U) (a : U),
    (∀ x, mem x a → ∃ y, Eval mem p (cons y (cons x v))) →
    ∃ b, ∀ x, mem x a → ∃ y, mem y b ∧ Eval mem p (cons y (cons x v))

def Replacement (mem : U → U → Prop) : Prop :=
  ∀ n (p : Formula (n + 2)) (v : Fin n → U) (a : U),
    (∀ x, mem x a → ∃ y, Eval mem p (cons y (cons x v)) ∧
      ∀ z, Eval mem p (cons z (cons x v)) → z = y) →
    ∃ b, ∀ y, mem y b ↔ ∃ x, mem x a ∧ Eval mem p (cons y (cons x v))

theorem collection_separation_replacement (mem : U → U → Prop)
    (hc : Collection mem) (hs : Separation mem) : Replacement mem := by
  intro n p v a hfun
  obtain ⟨b, hb⟩ := hc n p v a (by
    intro x hx
    obtain ⟨y, hy, _⟩ := hfun x hx
    exact ⟨y, hy⟩)
  obtain ⟨c, hsep⟩ := hs (n + 1) (imageFormula p) (cons a v) b
  refine ⟨c, ?_⟩
  intro y
  constructor
  · intro hy
    exact (eval_image mem p y a v).mp ((hsep y).mp hy).2
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨z, hz, hxz⟩ := hb x hx
    obtain ⟨w, _, hw⟩ := hfun x hx
    have hyz : y = z := (hw y hxy).trans (hw z hxz).symm
    apply (hsep y).mpr
    constructor
    · exact hyz ▸ hz
    · exact (eval_image mem p y a v).mpr ⟨x, hx, hxy⟩

#print axioms collection_separation_replacement
end FullBridge
