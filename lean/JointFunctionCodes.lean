import MaskChoiceCandidate
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Actual graph comprehension for a source formula with a unique value on
    each member of a source set. No object-level choice is required. -/
theorem definable_function_code (base : BaseCollection s) {n} (p : Formula (n+2))
    (v : Fin n → U) (d : U)
    (ht : ∀ x, s x d → ∃ y, Eval s p (cons y (cons x v)) ∧
      ∀ z, Eval s p (cons z (cons x v)) → z = y) :
    ∃ f, FunctionCode s d f ∧ ∀ x y,
      CodedRelation s f x y ↔ s x d ∧ Eval s p (cons y (cons x v)) := by
  obtain ⟨r, hr⟩ := collection_separation_replacement s base.collection base.separation n p v d ht
  obtain ⟨b, hb⟩ := binary_union_exists base.pairing base.union d r
  let q : Formula (n+3) := .conj (.member 1 2)
    (p.rename (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ))))
  have hev : ∀ x y, Eval s q (cons y (cons x (cons d v))) ↔
      s x d ∧ Eval s p (cons y (cons x v)) := by
    intro x y
    simp only [q, Eval, eval_rename]
    have he : (fun i => cons y (cons x (cons d v))
        (Fin.cases 0 (Fin.cases 1 (fun j => j.succ.succ.succ)) i)) = cons y (cons x v) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
    rw [he]
    rfl
  obtain ⟨f, hG, hrel⟩ := normalized_relation_comprehension base q (cons d v) b
  have hf : ∀ x y, CodedRelation s f x y ↔ s x d ∧ Eval s p (cons y (cons x v)) := by
    intro x y
    constructor
    · intro h
      exact (hev x y).mp ((hrel x y).mp h).2.2
    · rintro ⟨hx, hp⟩
      exact (hrel x y).mpr ⟨(hb x).mpr (Or.inl hx),
        (hb y).mpr (Or.inr ((hr y).mpr ⟨x, hx, hp⟩)), (hev x y).mpr ⟨hx, hp⟩⟩
  refine ⟨f, ⟨?_, ?_⟩, hf⟩
  · intro a ha
    obtain ⟨x, y, _, _, hxy⟩ := hG a ha
    exact ⟨x, y, ((hf x y).mp ⟨a, ha, hxy⟩).1, hxy⟩
  · intro x hx
    obtain ⟨y, hy, hu⟩ := ht x hx
    exact ⟨y, (hf x y).mpr ⟨hx, hy⟩, fun z hz => hu z ((hf x z).mp hz).2⟩

/-- Free variables [graph,domain,parameters]; p has [output,input,parameters]. -/
def definedFunctionGraphFormula {n} (p : Formula (n+2)) : Formula (n+2) :=
  .conj (functionCodeFormula 1 0) (.all (.all
    ((relatedFormula 2 1 0).iffF (.conj (.member 1 3) (p.rename relationRename)))))

def DefinedFunctionGraph (s : U → U → Prop) {n} (p : Formula (n+2))
    (v : Fin n → U) (d f : U) : Prop :=
  FunctionCode s d f ∧ ∀ x y, CodedRelation s f x y ↔ s x d ∧ Eval s p (cons y (cons x v))

theorem eval_definedFunctionGraphFormula {n} (p : Formula (n+2)) (v : Fin n → U) (d f : U) :
    Eval s (definedFunctionGraphFormula p) (cons f (cons d v)) ↔ DefinedFunctionGraph s p v d f := by
  simp only [definedFunctionGraphFormula, Eval, eval_functionCodeFormula, eval_iffF, eval_relatedFormula,
    eval_rename, relation_env, DefinedFunctionGraph]
  rfl

theorem defined_function_graph_unique (base : BaseCollection s) {n} {p : Formula (n+2)}
    {v : Fin n → U} {d f g : U} (hf : DefinedFunctionGraph s p v d f)
    (hg : DefinedFunctionGraph s p v d g) : f = g := by
  apply function_code_extensional base.extensional hf.1 hg.1
  intro x y z hxy hxz
  have hy := ((hf.2 x y).mp hxy).2
  have hz := ((hg.2 x z).mp hxz).2
  have hz' := (hf.2 x z).mpr ⟨coded_function_domain hg.1 hxz, hz⟩
  exact coded_function_value_unique hf.1 hxy hz'
end FullBridge
