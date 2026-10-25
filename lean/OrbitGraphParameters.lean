import JointMaskRestrictions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The orbit index is the actual triple (fixed part,nodes,edges), not a
    mask name. Equal parameter triples consequently give one component. -/
def OrbitGraphParameters (s : U → U → Prop) (p t a r : U) : Prop :=
  ∃ b, IsOrderedPair s b a r ∧ IsOrderedPair s p t b

def orbitGraphParametersFormula {n} (p t a r : Fin n) : Formula n :=
  .ex (.conj (orderedPairFormula 0 a.succ r.succ) (orderedPairFormula p.succ t.succ 0))

theorem eval_orbitGraphParametersFormula {n} (p t a r : Fin n) (v : Fin n → U) :
    Eval s (orbitGraphParametersFormula p t a r) v ↔
      OrbitGraphParameters s (v p) (v t) (v a) (v r) := by
  simp only [orbitGraphParametersFormula, Eval, eval_orderedPairFormula, OrbitGraphParameters]
  rfl

theorem orbit_graph_parameters_exists (base : BaseCollection s) (t a r : U) :
    ∃ p, OrbitGraphParameters s p t a r := by
  obtain ⟨b, hb⟩ := orderedPair_exists base.pairing a r
  obtain ⟨p, hp⟩ := orderedPair_exists base.pairing t b
  exact ⟨p, b, hb, hp⟩

theorem orbit_graph_parameters_unique {p t a r t' a' r' : U}
    (h : OrbitGraphParameters s p t a r) (h' : OrbitGraphParameters s p t' a' r') :
    t = t' ∧ a = a' ∧ r = r' := by
  obtain ⟨b, hb, hp⟩ := h
  obtain ⟨b', hb', hp'⟩ := h'
  obtain ⟨htt', hbb'⟩ := orderedPair_injective hp hp'
  obtain ⟨haa', hrr'⟩ := orderedPair_injective (hbb' ▸ hb) hb'
  exact ⟨htt', haa', hrr'⟩

theorem elementary_map_graph_parameters {j : U → U} (hj : ElementaryMap s s j)
    {p t a r : U} (h : OrbitGraphParameters s p t a r) :
    OrbitGraphParameters s (j p) (j t) (j a) (j r) := by
  obtain ⟨b, hb, hp⟩ := h
  exact ⟨j b, elementary_map_ordered_pair hj hb, elementary_map_ordered_pair hj hp⟩

theorem ordered_pair_components_in_transitive {B p x y : U} (hB : TransitiveCode s B)
    (hpB : s p B) (hp : IsOrderedPair s p x y) : s x B ∧ s y B := by
  obtain ⟨a, b, _, hb, hp⟩ := hp
  have hbB := hB p hpB b ((hp b).mpr (Or.inr rfl))
  exact ⟨hB b hbB x ((hb x).mpr (Or.inl rfl)), hB b hbB y ((hb y).mpr (Or.inr rfl))⟩

theorem orbit_graph_parameters_in_transitive {B p t a r : U} (hB : TransitiveCode s B)
    (hpB : s p B) (hp : OrbitGraphParameters s p t a r) : s t B ∧ s a B ∧ s r B := by
  obtain ⟨b, hb, hp⟩ := hp
  have h := ordered_pair_components_in_transitive hB hpB hp
  exact ⟨h.1, ordered_pair_components_in_transitive hB h.2 hb⟩

def BafaRequestCode (s : U → U → Prop) (p : U) : Prop :=
  ∃ t a r, OrbitGraphParameters s p t a r ∧ TransitiveCode s t ∧ GraphCode s a r ∧
    GraphExtensionalCode s a r ∧ EndExtensionCode s a r t

def bafaRequestFormula {n} (p : Fin n) : Formula n :=
  .ex (.ex (.ex (.conj (orbitGraphParametersFormula p.succ.succ.succ 2 1 0)
    (.conj (transitiveFormula 2) (.conj (graphCodeFormula 1 0)
      (.conj (graphExtensionalFormula 1 0) (endExtensionFormula 1 0 2)))))))

theorem eval_bafaRequestFormula {n} (p : Fin n) (v : Fin n → U) :
    Eval s (bafaRequestFormula p) v ↔ BafaRequestCode s (v p) := by
  simp only [bafaRequestFormula, Eval, eval_orbitGraphParametersFormula, eval_transitiveFormula,
    eval_graphCodeFormula, eval_graphExtensionalFormula, eval_endExtensionFormula, BafaRequestCode]
  rfl

theorem elementary_map_bafa_request {j : U → U} (hj : ElementaryMap s s j) (p : U) :
    BafaRequestCode s p ↔ BafaRequestCode s (j p) := by
  have h := hj (bafaRequestFormula (n := 1) 0) (cons p Fin.elim0)
  rw [eval_bafaRequestFormula, eval_bafaRequestFormula] at h
  exact h

theorem bafa_request_parameters {p t a r : U} (hp : BafaRequestCode s p)
    (h : OrbitGraphParameters s p t a r) :
    TransitiveCode s t ∧ GraphCode s a r ∧ GraphExtensionalCode s a r ∧ EndExtensionCode s a r t := by
  obtain ⟨t', a', r', h', ht', hG', hExt', hEnd'⟩ := hp
  obtain ⟨rfl, rfl, rfl⟩ := orbit_graph_parameters_unique h h'
  exact ⟨ht', hG', hExt', hEnd'⟩

#print axioms elementary_map_bafa_request
end FullBridge
