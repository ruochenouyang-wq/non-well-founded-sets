import JointMaskPowerTowers
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def indexedFunctionGraphFormula {n} (p : Formula (n+3)) : Formula (n+3) :=
  (definedFunctionGraphFormula p).rename
    (Fin.cases 0 (Fin.cases 2 (Fin.cases 1 (fun i => i.succ.succ.succ))))

theorem eval_indexedFunctionGraphFormula {n} (p : Formula (n+3))
    (v : Fin n → U) (f i d : U) :
    Eval s (indexedFunctionGraphFormula p) (cons f (cons i (cons d v))) ↔
      DefinedFunctionGraph s p (cons i v) d f := by
  rw [indexedFunctionGraphFormula, eval_rename]
  have he : (fun j => cons f (cons i (cons d v))
      (Fin.cases 0 (Fin.cases 2 (Fin.cases 1 (fun k => k.succ.succ.succ))) j)) =
      cons f (cons d (cons i v)) := by
    funext j
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) j) j
  rw [he]
  exact eval_definedFunctionGraphFormula p (cons i v) d f

/-- A single source function collects a source-set-indexed family of
    uniquely formula-defined function graphs. -/
theorem definable_function_family (base : BaseCollection s) {n} (p : Formula (n+3))
    (v : Fin n → U) (G d : U)
    (ht : ∀ i, s i G → ∀ x, s x d → ∃ y, Eval s p (cons y (cons x (cons i v))) ∧
      ∀ z, Eval s p (cons z (cons x (cons i v))) → z = y) :
    ∃ K, FunctionCode s G K ∧ ∀ i f, CodedRelation s K i f ↔
      s i G ∧ DefinedFunctionGraph s p (cons i v) d f := by
  have hgraphs : ∀ i, s i G → ∃ f, Eval s (indexedFunctionGraphFormula p) (cons f (cons i (cons d v))) ∧
      ∀ g, Eval s (indexedFunctionGraphFormula p) (cons g (cons i (cons d v))) → g = f := by
    intro i hi
    obtain ⟨f, hf⟩ := definable_function_code base p (cons i v) d (ht i hi)
    exact ⟨f, (eval_indexedFunctionGraphFormula p v f i d).mpr hf,
      fun g hg => defined_function_graph_unique base ((eval_indexedFunctionGraphFormula p v g i d).mp hg) hf⟩
  obtain ⟨K, hK, hrel⟩ := definable_function_code base (indexedFunctionGraphFormula p) (cons d v) G hgraphs
  exact ⟨K, hK, fun i f => (hrel i f).trans (and_congr Iff.rfl (eval_indexedFunctionGraphFormula p v f i d))⟩
end FullBridge
