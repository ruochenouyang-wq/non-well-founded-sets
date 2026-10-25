import PrunedExtensionalRealization
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Inside c compare the coded map values; outside c impose no restriction. -/
def closedMapKernelFormula : Formula 4 :=
  .impl (.conj (.member 1 2) (.member 0 2))
    (.ex (.conj (relatedFormula 4 2 0) (relatedFormula 4 1 0)))

theorem eval_closedMapKernelFormula (c h x y : U) :
    Eval s closedMapKernelFormula (cons y (cons x (cons c (cons h Fin.elim0)))) ↔
      (s x c ∧ s y c → ∃ z, CodedRelation s h x z ∧ CodedRelation s h y z) := by
  simp only [closedMapKernelFormula, Eval, eval_relatedFormula]
  rfl

/-- A closed graph may have several representatives for each target node.
    Exact rows and target extensionality suffice to prevent the least quotient
    from identifying different coded-map values. -/
theorem global_least_conserves_closed_map (base : BaseCollection s) {n}
    (p : Formula (n + 2)) (params : Fin n → U)
    (hmem : ∀ x y, FormulaEdges s p params x y → s y x)
    {c a e h : U} (hf : FunctionCode s c h)
    (hrange : ∀ x v, CodedRelation s h x v → s v a)
    (hclosed : ∀ x, s x c → ∀ y, FormulaEdges s p params x y → s y c)
    (hext : GraphExtensionalCode s a e)
    (hrows : ∀ x v, s x c → CodedRelation s h x v → ∀ w, s w a →
      (CodedRelation s e v w ↔ ∃ y, FormulaEdges s p params x y ∧ CodedRelation s h y w))
    {x y v w : U} (hxv : CodedRelation s h x v) (hyw : CodedRelation s h y w)
    (hxy : DefinedLeastRelation s p params x y) : v = w := by
  let K := fun x y => s x c ∧ s y c → ∃ z, CodedRelation s h x z ∧ CodedRelation s h y z
  have hrefl : ∀ x, K x x := by
    intro x hx
    obtain ⟨z, hxz, _⟩ := hf.2 x hx.1
    exact ⟨z, hxz, hxz⟩
  have hpre : ∀ x y,
      ((∀ u, FormulaEdges s p params x u → ∃ v', FormulaEdges s p params y v' ∧ K u v') ∧
       (∀ v', FormulaEdges s p params y v' → ∃ u, FormulaEdges s p params x u ∧ K u v')) → K x y := by
    intro x y hmatch hinc
    obtain ⟨i, hxi, _⟩ := hf.2 x hinc.1
    obtain ⟨j, hyj, _⟩ := hf.2 y hinc.2
    have hij : i = j := by
      apply hext i (hrange x i hxi) j (hrange y j hyj)
      intro z hz
      constructor
      · intro hiz
        obtain ⟨u, hxu, huz⟩ := (hrows x i hinc.1 hxi z hz).mp hiz
        obtain ⟨v', hyv, huv⟩ := hmatch.1 u hxu
        obtain ⟨k, huk, hvk⟩ := huv ⟨hclosed x hinc.1 u hxu, hclosed y hinc.2 v' hyv⟩
        have hzk := coded_function_value_unique hf huz huk
        exact (hrows y j hinc.2 hyj z hz).mpr ⟨v', hyv, hzk.symm ▸ hvk⟩
      · intro hjz
        obtain ⟨v', hyv, hvz⟩ := (hrows y j hinc.2 hyj z hz).mp hjz
        obtain ⟨u, hxu, huv⟩ := hmatch.2 v' hyv
        obtain ⟨k, huk, hvk⟩ := huv ⟨hclosed x hinc.1 u hxu, hclosed y hinc.2 v' hyv⟩
        have hzk := coded_function_value_unique hf hvz hvk
        exact (hrows x i hinc.1 hxi z hz).mpr ⟨u, hxu, hzk.symm ▸ huk⟩
    exact ⟨j, hij ▸ hxi, hyj⟩
  have hsub := defined_least_minimal_definable base p params hmem closedMapKernelFormula
    (cons c (cons h Fin.elim0)) (by
      intro x
      exact (eval_closedMapKernelFormula c h x x).mpr (hrefl x)) (by
      intro x y hmatch
      apply (eval_closedMapKernelFormula c h x y).mpr
      apply hpre x y
      constructor
      · intro u hxu
        obtain ⟨v', hyv, huv⟩ := hmatch.1 u hxu
        exact ⟨v', hyv, (eval_closedMapKernelFormula c h u v').mp huv⟩
      · intro v' hyv
        obtain ⟨u, hxu, huv⟩ := hmatch.2 v' hyv
        exact ⟨u, hxu, (eval_closedMapKernelFormula c h u v').mp huv⟩)
  obtain ⟨z, hxz, hyz⟩ := (eval_closedMapKernelFormula c h x y).mp (hsub x y hxy)
    ⟨coded_function_domain hf hxv, coded_function_domain hf hyw⟩
  exact (coded_function_value_unique hf hxv hxz).trans (coded_function_value_unique hf hyw hyz).symm

theorem pruned_code_conserves_closed_map (base : BaseCollection s) {b c a e h : U}
    (hf : FunctionCode s c h) (hrange : ∀ x v, CodedRelation s h x v → s v a)
    (hclosed : ∀ x, s x c → ∀ y, PrunedMember s b x y → s y c)
    (hext : GraphExtensionalCode s a e)
    (hrows : ∀ x v, s x c → CodedRelation s h x v → ∀ w, s w a →
      (CodedRelation s e v w ↔ ∃ y, PrunedMember s b x y ∧ CodedRelation s h y w))
    {x y v w : U} (hxv : CodedRelation s h x v) (hyw : CodedRelation s h y w)
    (hxy : prunedCode base b x = prunedCode base b y) : v = w :=
  global_least_conserves_closed_map base prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) hf hrange hclosed hext hrows hxv hyw
    ((least_global_code_eq base prunedMemberFormula (cons b Fin.elim0)
      (pruned_edges_are_members b) x y).mp hxy)

#print axioms pruned_code_conserves_closed_map
end FullBridge
