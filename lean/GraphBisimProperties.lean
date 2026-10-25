import GraphBisimulation

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem maximal_graph_bisim_refl (base : BaseCollection s) {a e m : U}
    (hG : GraphCode s a e) (hm : MaxGraphBisimCode s a e m)
    {x : U} (hx : s x a) : CodedRelation s m x x := by
  obtain ⟨d, hdG, hd⟩ := normalized_relation_comprehension base
    (Formula.equal (n := 2) 0 1) Fin.elim0 a
  have hdB : GraphBisimCode s a e d := by
    refine ⟨hdG, ?_⟩
    intro u v huv
    obtain ⟨_, _, heq⟩ := (hd u v).mp huv
    change v = u at heq
    subst v
    constructor <;> intro z hz
    · exact ⟨z, hz, (hd z z).mpr ⟨(graphCode_endpoints hG hz).2,
        (graphCode_endpoints hG hz).2, rfl⟩⟩
    · exact ⟨z, hz, (hd z z).mpr ⟨(graphCode_endpoints hG hz).2,
        (graphCode_endpoints hG hz).2, rfl⟩⟩
  exact hm.2 d hdB x x ((hd x x).mpr ⟨hx, hx, rfl⟩)

theorem maximal_graph_bisim_symm (base : BaseCollection s) {a e m x y : U}
    (hm : MaxGraphBisimCode s a e m) (hxy : CodedRelation s m x y) :
    CodedRelation s m y x := by
  obtain ⟨r, hG, hr⟩ := normalized_relation_comprehension base
    (relatedFormula (n := 3) 2 0 1) (cons m Fin.elim0) a
  have hi : ∀ u v, CodedRelation s r u v ↔ CodedRelation s m v u := by
    intro u v
    have hh := hr u v
    rw [eval_relatedFormula] at hh
    constructor
    · intro h
      exact ((hh.mp h).2).2
    · intro h
      have hb := graphCode_endpoints hm.1.1 h
      exact hh.mpr ⟨hb.2, hb.1, h⟩
  have hB : GraphBisimCode s a e r := by
    refine ⟨hG, ?_⟩
    apply bisimulation_congr (fun u v => (hi u v).symm)
    intro u v h
    exact ⟨(hm.1.2 v u h).2, (hm.1.2 v u h).1⟩
  exact hm.2 r hB y x ((hi y x).mpr hxy)

theorem maximal_graph_bisim_trans (base : BaseCollection s) {a e m x y z : U}
    (hm : MaxGraphBisimCode s a e m) (hxy : CodedRelation s m x y)
    (hyz : CodedRelation s m y z) : CodedRelation s m x z := by
  obtain ⟨r, hG, hr⟩ := normalized_relation_comprehension base compositionFormula
    (cons m (cons m Fin.elim0)) a
  have hi : ∀ u v, CodedRelation s r u v ↔ ∃ w, CodedRelation s m u w ∧ CodedRelation s m w v := by
    intro u v
    have hh := hr u v
    rw [eval_compositionFormula] at hh
    constructor
    · intro h
      exact ((hh.mp h).2).2
    · rintro ⟨w, huw, hwv⟩
      exact hh.mpr ⟨(graphCode_endpoints hm.1.1 huw).1,
        (graphCode_endpoints hm.1.1 hwv).2, w, huw, hwv⟩
  have hB : GraphBisimCode s a e r :=
    ⟨hG, bisimulation_congr (fun u v => (hi u v).symm) (bisimulation_comp hm.1.2 hm.1.2)⟩
  exact hm.2 r hB x z ((hi x z).mpr ⟨y, hxy, hyz⟩)

def graphRootFormula : Formula 5 :=
  (relatedFormula 2 1 0).disj (.conj (.equal 1 3) (.equal 0 4))

theorem eval_graphRootFormula (u v m x y : U) :
    Eval s graphRootFormula (cons v (cons u (cons m (cons x (cons y Fin.elim0))))) ↔
      CodedRelation s m u v ∨ (u = x ∧ v = y) := by
  simp only [graphRootFormula, eval_disj, Eval, eval_relatedFormula]
  rfl

theorem maximal_graph_bisim_of_children (base : BaseCollection s) {a e m x y : U}
    (hm : MaxGraphBisimCode s a e m) (hx : s x a) (hy : s y a)
    (hf : ∀ u, CodedRelation s e x u → ∃ v, CodedRelation s e y v ∧ CodedRelation s m u v)
    (hb : ∀ v, CodedRelation s e y v → ∃ u, CodedRelation s e x u ∧ CodedRelation s m u v) :
    CodedRelation s m x y := by
  obtain ⟨r, hG, hr⟩ := normalized_relation_comprehension base graphRootFormula
    (cons m (cons x (cons y Fin.elim0))) a
  have hi : ∀ u v, CodedRelation s r u v ↔ CodedRelation s m u v ∨ (u = x ∧ v = y) := by
    intro u v
    have hh := hr u v
    rw [eval_graphRootFormula] at hh
    constructor
    · intro h
      exact ((hh.mp h).2).2
    · intro h
      rcases h with h | ⟨rfl, rfl⟩
      · have hd := graphCode_endpoints hm.1.1 h
        exact hh.mpr ⟨hd.1, hd.2, Or.inl h⟩
      · exact hh.mpr ⟨hx, hy, Or.inr ⟨rfl, rfl⟩⟩
  have hB : GraphBisimCode s a e r := by
    refine ⟨hG, ?_⟩
    intro u v huv
    have hmatch :
        (∀ z, CodedRelation s e u z → ∃ w, CodedRelation s e v w ∧ CodedRelation s m z w) ∧
        (∀ w, CodedRelation s e v w → ∃ z, CodedRelation s e u z ∧ CodedRelation s m z w) := by
      rcases (hi u v).mp huv with h | ⟨rfl, rfl⟩
      · exact hm.1.2 u v h
      · exact ⟨hf, hb⟩
    constructor
    · intro z hz
      obtain ⟨w, hw, hzw⟩ := hmatch.1 z hz
      exact ⟨w, hw, (hi z w).mpr (Or.inl hzw)⟩
    · intro w hw
      obtain ⟨z, hz, hzw⟩ := hmatch.2 w hw
      exact ⟨z, hz, (hi z w).mpr (Or.inl hzw)⟩
  exact hm.2 r hB x y ((hi x y).mpr (Or.inr ⟨rfl, rfl⟩))

#print axioms maximal_graph_bisim_of_children
end FullBridge
