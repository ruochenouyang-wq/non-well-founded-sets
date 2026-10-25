import BoffaSyntax

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def GraphBisimCode (s : U → U → Prop) (a e r : U) : Prop :=
  GraphCode s a r ∧ Bisimulation (fun x y => CodedRelation s e y x) (CodedRelation s r)

def graphBisimFormula {n} (a e r : Fin n) : Formula n :=
  .conj (graphCodeFormula a r)
    (.all (.all (.impl (relatedFormula r.succ.succ 1 0)
      (.conj
        (.all (.impl (relatedFormula e.succ.succ.succ 2 0)
          (.ex (.conj (relatedFormula e.succ.succ.succ.succ 2 0)
            (relatedFormula r.succ.succ.succ.succ 1 0)))))
        (.all (.impl (relatedFormula e.succ.succ.succ 1 0)
          (.ex (.conj (relatedFormula e.succ.succ.succ.succ 3 0)
            (relatedFormula r.succ.succ.succ.succ 0 1)))))))))

theorem eval_graphBisimFormula (s : U → U → Prop) {n}
    (a e r : Fin n) (v : Fin n → U) :
    Eval s (graphBisimFormula a e r) v ↔ GraphBisimCode s (v a) (v e) (v r) := by
  simp only [graphBisimFormula, Eval, eval_graphCodeFormula, eval_relatedFormula,
    GraphBisimCode, Bisimulation, cons_succ]
  rfl

theorem graphCode_endpoints {a r x y : U} (hG : GraphCode s a r)
    (h : CodedRelation s r x y) : s x a ∧ s y a := by
  obtain ⟨p, hpr, hp⟩ := h
  obtain ⟨u, v, hu, hv, hp'⟩ := hG p hpr
  obtain ⟨rfl, rfl⟩ := orderedPair_injective hp hp'
  exact ⟨hu, hv⟩

theorem normalized_relation_comprehension (base : BaseCollection s)
    {n} (p : Formula (n + 2)) (v : Fin n → U) (a : U) :
    ∃ r, GraphCode s a r ∧ ∀ x y, CodedRelation s r x y ↔
      s x a ∧ s y a ∧ Eval s p (cons y (cons x v)) := by
  obtain ⟨r, hr⟩ := relation_comprehension_members base p v a
  refine ⟨r, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, y, hx, hy, hp, _⟩ := (hr z).mp hz
    exact ⟨x, y, hx, hy, hp⟩
  · intro x y
    constructor
    · rintro ⟨z, hz, hzxy⟩
      obtain ⟨x', y', hx, hy, hz', hxy⟩ := (hr z).mp hz
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hzxy hz'
      exact ⟨hx, hy, hxy⟩
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨z, hz⟩ := orderedPair_exists base.pairing x y
      exact ⟨z, (hr z).mpr ⟨x, y, hx, hy, hz, hxy⟩, hz⟩

def MaxGraphBisimCode (s : U → U → Prop) (a e r : U) : Prop :=
  GraphBisimCode s a e r ∧ ∀ t, GraphBisimCode s a e t →
    ∀ x y, CodedRelation s t x y → CodedRelation s r x y

theorem maximal_graph_bisim_exists (base : BaseCollection s) (a e : U) :
    ∃ r, MaxGraphBisimCode s a e r := by
  obtain ⟨pa, hpa⟩ := base.powerset a
  obtain ⟨ppa, hppa⟩ := base.powerset pa
  obtain ⟨pppa, hpppa⟩ := base.powerset ppa
  obtain ⟨b, hb⟩ := base.separation 2 (graphBisimFormula 1 2 0)
    (cons a (cons e Fin.elim0)) pppa
  have hbiff : ∀ t, s t b ↔ Subset s t ppa ∧ GraphBisimCode s a e t := by
    intro t
    have ht := hb t
    rw [hpppa, eval_graphBisimFormula] at ht
    exact ht
  obtain ⟨r, hr⟩ := base.union b
  have hrel : ∀ x y, CodedRelation s r x y ↔ ∃ t, s t b ∧ CodedRelation s t x y := by
    intro x y
    constructor
    · rintro ⟨p, hpr, hp⟩
      obtain ⟨t, htb, hpt⟩ := (hr p).mp hpr
      exact ⟨t, htb, p, hpt, hp⟩
    · rintro ⟨t, htb, p, hpt, hp⟩
      exact ⟨p, (hr p).mpr ⟨t, htb, hpt⟩, hp⟩
  refine ⟨r, ⟨?_, ?_⟩, ?_⟩
  · intro p hpr
    obtain ⟨t, htb, hpt⟩ := (hr p).mp hpr
    exact ((hbiff t).mp htb).2.1 p hpt
  · intro x y hxy
    obtain ⟨t, htb, htxy⟩ := (hrel x y).mp hxy
    have ht := ((hbiff t).mp htb).2.2 x y htxy
    constructor
    · intro u hu
      obtain ⟨v, hv, huv⟩ := ht.1 u hu
      exact ⟨v, hv, (hrel u v).mpr ⟨t, htb, huv⟩⟩
    · intro v hv
      obtain ⟨u, hu, huv⟩ := ht.2 v hv
      exact ⟨u, hu, (hrel u v).mpr ⟨t, htb, huv⟩⟩
  · intro t ht x y hxy
    have hbound : Subset s t ppa := by
      intro p hpt
      obtain ⟨u, v, hu, hv, hp⟩ := ht.1 p hpt
      exact orderedPair_bound hpa hppa hu hv hp
    exact (hrel x y).mpr ⟨t, (hbiff t).mpr ⟨hbound, ht⟩, hxy⟩

#print axioms maximal_graph_bisim_exists
end FullBridge
