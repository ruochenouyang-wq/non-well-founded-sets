import GraphBisimProperties

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def GraphClassCode (s : U → U → Prop) (a m x c : U) : Prop :=
  ∀ z, s z c ↔ s z a ∧ CodedRelation s m x z

def graphClassFormula {n} (c x a m : Fin n) : Formula n :=
  .all ((Formula.member 0 c.succ).iffF
    (.conj (.member 0 a.succ) (relatedFormula m.succ x.succ 0)))

theorem eval_graphClassFormula {n} (c x a m : Fin n) (v : Fin n → U) :
    Eval s (graphClassFormula c x a m) v ↔ GraphClassCode s (v a) (v m) (v x) (v c) := by
  simp only [graphClassFormula, Eval, eval_iffF, eval_relatedFormula, cons_succ]
  rfl

theorem graph_class_exists (base : BaseCollection s) (a m x : U) :
    ∃ c, GraphClassCode s a m x c := by
  obtain ⟨c, hc⟩ := base.separation 2 (relatedFormula 2 1 0)
    (cons x (cons m Fin.elim0)) a
  refine ⟨c, ?_⟩
  intro z
  have h := hc z
  rw [eval_relatedFormula] at h
  exact h

theorem graph_class_unique (base : BaseCollection s) {a m x c d : U}
    (hc : GraphClassCode s a m x c) (hd : GraphClassCode s a m x d) : c = d := by
  apply base.extensional
  intro z
  exact (hc z).trans (hd z).symm

theorem graph_class_eq_iff (base : BaseCollection s) {a e m x y c d : U}
    (hG : GraphCode s a e) (hm : MaxGraphBisimCode s a e m)
    (hx : s x a) (_hy : s y a)
    (hc : GraphClassCode s a m x c) (hd : GraphClassCode s a m y d) :
    c = d ↔ CodedRelation s m x y := by
  constructor
  · intro heq
    have hxc := (hc x).mpr ⟨hx, maximal_graph_bisim_refl base hG hm hx⟩
    rw [heq] at hxc
    exact maximal_graph_bisim_symm base hm ((hd x).mp hxc).2
  · intro hxy
    apply base.extensional
    intro z
    rw [hc z, hd z]
    constructor
    · rintro ⟨hz, hxz⟩
      exact ⟨hz, maximal_graph_bisim_trans base hm
        (maximal_graph_bisim_symm base hm hxy) hxz⟩
    · rintro ⟨hz, hyz⟩
      exact ⟨hz, maximal_graph_bisim_trans base hm hxy hyz⟩

def graphClassNodeFormula : Formula 3 :=
  .ex (.conj (.member 0 2) (graphClassFormula 1 0 2 3))

theorem eval_graphClassNodeFormula (c a m : U) :
    Eval s graphClassNodeFormula (cons c (cons a (cons m Fin.elim0))) ↔
      ∃ x, s x a ∧ GraphClassCode s a m x c := by
  simp only [graphClassNodeFormula, Eval, eval_graphClassFormula]
  rfl

theorem graph_class_nodes_exists (base : BaseCollection s) (a m : U) :
    ∃ b, ∀ c, s c b ↔ ∃ x, s x a ∧ GraphClassCode s a m x c := by
  obtain ⟨pa, hpa⟩ := base.powerset a
  obtain ⟨b, hb⟩ := base.separation 2 graphClassNodeFormula
    (cons a (cons m Fin.elim0)) pa
  refine ⟨b, ?_⟩
  intro c
  have h := hb c
  rw [eval_graphClassNodeFormula] at h
  constructor
  · intro hc
    exact (h.mp hc).2
  · rintro ⟨x, hx, hc⟩
    exact h.mpr ⟨(hpa c).mpr (fun z hz => ((hc z).mp hz).1), x, hx, hc⟩

#print axioms graph_class_nodes_exists
#print axioms graph_class_eq_iff
end FullBridge
