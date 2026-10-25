import NonstandardSupportedPowerFailure
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The bound and every index are objects of the source model. -/
def RowTailBalanced (s : U → U → Prop) (w left right N a : U) : Prop :=
  ∀ i, s i w → ¬s i N → ∀ l r,
    CodedRelation s left i l → CodedRelation s right i r → (s l a ↔ s r a)

def InternallyBoundedRowSupport (s : U → U → Prop) (w left right a : U) : Prop :=
  ∃ N, s N w ∧ RowTailBalanced s w left right N a

def rowTailBalancedFormula {n} (w left right N a : Fin n) : Formula n :=
  .all (.impl (.member 0 w.succ) (.impl (.impl (.member 0 N.succ) .bottom)
    (.all (.all (.impl (relatedFormula left.succ.succ.succ 2 1)
      (.impl (relatedFormula right.succ.succ.succ 2 0)
        ((Formula.member 1 a.succ.succ.succ).iffF (.member 0 a.succ.succ.succ))))))))

def internallyBoundedRowSupportFormula {n} (w left right a : Fin n) : Formula n :=
  .ex (.conj (.member 0 w.succ) (rowTailBalancedFormula w.succ left.succ right.succ 0 a.succ))

theorem eval_rowTailBalancedFormula {n} (w left right N a : Fin n) (v : Fin n → U) :
    Eval s (rowTailBalancedFormula w left right N a) v ↔
      RowTailBalanced s (v w) (v left) (v right) (v N) (v a) := by
  simp only [rowTailBalancedFormula, Eval, eval_relatedFormula, eval_iffF, RowTailBalanced, cons_succ]
  rfl

theorem eval_internallyBoundedRowSupportFormula {n} (w left right a : Fin n) (v : Fin n → U) :
    Eval s (internallyBoundedRowSupportFormula w left right a) v ↔
      InternallyBoundedRowSupport s (v w) (v left) (v right) (v a) := by
  simp only [internallyBoundedRowSupportFormula, Eval, eval_rowTailBalancedFormula,
    InternallyBoundedRowSupport, cons_succ]
  rfl

theorem quine_swap_membership_invariant_iff {l r a : U} (hne : l ≠ r) :
    (∀ x, s (quineSwap l r x) a ↔ s x a) ↔ (s l a ↔ s r a) := by
  classical
  constructor
  · intro h
    simpa [quineSwap] using (h l).symm
  · intro h x
    by_cases hl : x = l
    · simpa [quineSwap, hl] using h.symm
    · by_cases hr : x = r
      · simpa [quineSwap, hr, Ne.symm hne] using h
      · simp [quineSwap, hl, hr]

/-- The exact supported-subset collection is a source set, obtained from
    its actual first-order definition. It is not yet a full submodel powerset. -/
theorem internally_supported_subsets_exist (base : BaseCollection s) (w left right d : U) :
    ∃ p, ∀ a, s a p ↔ Subset s a d ∧ InternallyBoundedRowSupport s w left right a := by
  obtain ⟨q, hq⟩ := base.powerset d
  obtain ⟨p, hp⟩ := base.separation 3 (internallyBoundedRowSupportFormula 1 2 3 0)
    (cons w (cons left (cons right Fin.elim0))) q
  exact ⟨p, fun a => (hp a).trans (and_congr (hq a)
    (eval_internallyBoundedRowSupportFormula 1 2 3 0 _))⟩

theorem internal_left_prefix_row_supported {w a L : U} (P : InternalQuinePairs s w)
    (ha : s a w) (hL : CodedImageSet s P.leftCode a L) :
    InternallyBoundedRowSupport s w P.leftCode P.rightCode L := by
  refine ⟨a, ha, ?_⟩
  intro i _ hin l r hl hr
  have hnl : ¬s l L := by
    intro h
    obtain ⟨j, hj, hjl⟩ := (hL l).mp h
    exact hin (P.leftInjective j i l hjl hl ▸ hj)
  have hnr : ¬s r L := by
    intro h
    obtain ⟨j, _, hjr⟩ := (hL r).mp h
    exact P.disjoint j i r hjr hr
  exact ⟨fun h => False.elim (hnl h), fun h => False.elim (hnr h)⟩

#print axioms internally_supported_subsets_exist
#print axioms internal_left_prefix_row_supported
end FullBridge
