import InternalIteration
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def FormulaEdges {n} (s : U → U → Prop) (p : Formula (n + 2))
    (v : Fin n → U) (x y : U) : Prop := Eval s p (cons y (cons x v))

theorem transitive_sets_cover (base : BaseCollection s) (x : U) :
    ∃ c, TransitiveCode s c ∧ s x c := by
  obtain ⟨a, ha⟩ := base.pairing x x
  obtain ⟨c, hc, hac⟩ := transitive_cover_exists base a
  exact ⟨c, hc, hac x ((ha x).mpr (Or.inl rfl))⟩

theorem transitive_sets_directed (base : BaseCollection s) {a b : U}
    (ha : TransitiveCode s a) (hb : TransitiveCode s b) :
    ∃ c, TransitiveCode s c ∧ Subset s a c ∧ Subset s b c := by
  obtain ⟨c, hc⟩ := binary_union_exists base.pairing base.union a b
  refine ⟨c, ?_, fun x hx => (hc x).mpr (Or.inl hx), fun x hx => (hc x).mpr (Or.inr hx)⟩
  intro x hx y hyx
  rcases (hc x).mp hx with hxa | hxb
  · exact (hc y).mpr (Or.inl (ha x hxa y hyx))
  · exact (hc y).mpr (Or.inr (hb x hxb y hyx))

/-- The cover is constructed from all actual internal transitive sets. The
    hypothesis concerns only the direction of graph edges, not cover existence. -/
noncomputable def definableMemberCover (base : BaseCollection s) {n}
    (p : Formula (n + 2)) (v : Fin n → U)
    (hmem : ∀ x y, FormulaEdges s p v x y → s y x) :
    ClosedLeastCover s (FormulaEdges s p v) {c : U // TransitiveCode s c} := by
  classical
  let edge := fun c : {c : U // TransitiveCode s c} =>
    Classical.choose (normalized_relation_comprehension base p v c.val)
  have hedge := fun c : {c : U // TransitiveCode s c} =>
    Classical.choose_spec (normalized_relation_comprehension base p v c.val)
  apply ClosedLeastCover.fromGraphs base Subtype.val edge
  · intro x
    obtain ⟨c, hc, hxc⟩ := transitive_sets_cover base x
    exact ⟨⟨c, hc⟩, hxc⟩
  · intro a b
    obtain ⟨c, hc, hac, hbc⟩ := transitive_sets_directed base a.property b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩
  · intro c x hx y hxy
    exact c.property x hx y (hmem x y hxy)
  · exact fun c => (hedge c).1
  · intro c x y
    exact ((hedge c).2 x y).trans
      ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, c.property x h.1 y (hmem x y h.2), h.2⟩⟩

def leastGraphFormula {n} (a e r : Fin n) : Formula n :=
  .conj (graphPreFixedFormula a e r)
    (.all (.impl (graphPreFixedFormula a.succ e.succ 0)
      (.all (.all (.impl (relatedFormula r.succ.succ.succ 1 0) (relatedFormula 2 1 0))))))

theorem eval_leastGraphFormula {n} (a e r : Fin n) (v : Fin n → U) :
    Eval s (leastGraphFormula a e r) v ↔ LeastGraphRelationCode s (v a) (v e) (v r) := by
  simp only [leastGraphFormula, Eval, eval_graphPreFixedFormula, eval_relatedFormula,
    LeastGraphRelationCode, cons_succ]
  rfl

def edgeInsertRename {n} : Fin (n + 2) → Fin (n + 4) :=
  Fin.cases 0 (Fin.cases 1 (fun j => j.succ.succ.succ.succ))

theorem edge_insert_env {n} (y x e c : U) (v : Fin n → U) :
    (fun j => cons y (cons x (cons e (cons c v))) (edgeInsertRename j)) = cons y (cons x v) := by
  funext j
  exact Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) j

def InducedEdgesCode {n} (s : U → U → Prop) (p : Formula (n + 2))
    (v : Fin n → U) (c e : U) : Prop :=
  GraphCode s c e ∧ ∀ x y, CodedRelation s e x y ↔ s x c ∧ s y c ∧ FormulaEdges s p v x y

/-- Free variables are [edge, nodes, parameters]. -/
def inducedEdgesFormula {n} (p : Formula (n + 2)) : Formula (n + 2) :=
  .conj (graphCodeFormula 1 0) (.all (.all
    ((relatedFormula 2 1 0).iffF (.conj (.member 1 3)
      (.conj (.member 0 3) (p.rename edgeInsertRename))))))

theorem eval_inducedEdgesFormula {n} (p : Formula (n + 2)) (e c : U) (v : Fin n → U) :
    Eval s (inducedEdgesFormula p) (cons e (cons c v)) ↔ InducedEdgesCode s p v c e := by
  simp only [inducedEdgesFormula, Eval, eval_graphCodeFormula, eval_iffF,
    eval_relatedFormula, eval_rename, edge_insert_env, InducedEdgesCode, FormulaEdges]
  rfl

def globalEdgeRename {n} : Fin (n + 2) → Fin (n + 5) :=
  Fin.cases 1 (Fin.cases 2 (fun j => j.succ.succ.succ.succ.succ))

theorem global_edge_env {n} (r e c y x : U) (v : Fin n → U) :
    (fun j => cons r (cons e (cons c (cons y (cons x v)))) (globalEdgeRename j)) =
      cons e (cons c v) := by
  funext j
  exact Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) j

def DefinedLeastRelation {n} (s : U → U → Prop) (p : Formula (n + 2))
    (v : Fin n → U) (x y : U) : Prop :=
  ∃ c e r, TransitiveCode s c ∧ s x c ∧ s y c ∧ InducedEdgesCode s p v c e ∧
    LeastGraphRelationCode s c e r ∧ CodedRelation s r x y

/-- Free variables are [second endpoint, first endpoint, parameters]. -/
def globalLeastFormula {n} (p : Formula (n + 2)) : Formula (n + 2) :=
  .ex (.ex (.ex (.conj (transitiveFormula 2) (.conj (.member 4 2) (.conj (.member 3 2)
    (.conj ((inducedEdgesFormula p).rename globalEdgeRename)
      (.conj (leastGraphFormula 2 1 0) (relatedFormula 0 4 3))))))))

theorem eval_globalLeastFormula {n} (p : Formula (n + 2)) (v : Fin n → U) (x y : U) :
    Eval s (globalLeastFormula p) (cons y (cons x v)) ↔ DefinedLeastRelation s p v x y := by
  simp only [globalLeastFormula, Eval, eval_transitiveFormula, eval_rename,
    global_edge_env, eval_inducedEdgesFormula, eval_leastGraphFormula,
    eval_relatedFormula, DefinedLeastRelation]
  rfl

theorem defined_least_iff_glued (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x) (x y : U) :
    DefinedLeastRelation s p v x y ↔ GluedLeastRelation (definableMemberCover base p v hmem) x y := by
  let C := definableMemberCover base p v hmem
  constructor
  · rintro ⟨c, e, r, hc, hx, hy, hE, hr, hxy⟩
    let i : {c : U // TransitiveCode s c} := ⟨c, hc⟩
    have hci : GraphClosedCode s (C.node i) (C.edge i) c :=
      ⟨fun _ h => h, fun u _ v huv => (graphCode_endpoints (C.graph i) huv).2⟩
    have heq : ∀ u v, CodedRelation s e u v ↔ s u c ∧ s v c ∧ CodedRelation s (C.edge i) u v := by
      intro u v
      rw [hE.2 u v, C.edge_iff i u v]
      exact ⟨fun h => ⟨h.1, h.2.1, h.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2.2⟩⟩
    exact ⟨i, hx, hy, (least_relation_closed_restriction base hci heq
      (C.minimal i) hr hx hy).mpr hxy⟩
  · rintro ⟨i, hx, hy, hxy⟩
    refine ⟨i.val, C.edge i, C.least i, i.property, hx, hy, ⟨C.graph i, ?_⟩, C.minimal i, hxy⟩
    intro u v
    exact (C.edge_iff i u v).trans
      ⟨fun h => ⟨h.1, i.property u h.1 v (hmem u v h.2), h.2⟩,
        fun h => ⟨h.1, h.2.2⟩⟩

theorem defined_least_equivalence (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x) :
    Equivalence (DefinedLeastRelation s p v) := by
  have hg := glued_least_equivalence base (definableMemberCover base p v hmem)
  have h := defined_least_iff_glued base p v hmem
  exact ⟨fun x => (h x x).mpr (hg.refl x),
    fun hxy => (h _ _).mpr (hg.symm ((h _ _).mp hxy)),
    fun hxy hyz => (h _ _).mpr (hg.trans ((h _ _).mp hxy) ((h _ _).mp hyz))⟩

theorem defined_least_fixed (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x) (x y : U) :
    DefinedLeastRelation s p v x y ↔
      (∀ u, FormulaEdges s p v x u → ∃ v', FormulaEdges s p v y v' ∧ DefinedLeastRelation s p v u v') ∧
      (∀ v', FormulaEdges s p v y v' → ∃ u, FormulaEdges s p v x u ∧ DefinedLeastRelation s p v u v') := by
  simpa only [defined_least_iff_glued base p v hmem] using
    (glued_least_fixed base (definableMemberCover base p v hmem) x y)

theorem defined_least_minimal_definable (base : BaseCollection s) {n k}
    (p : Formula (n + 2)) (v : Fin n → U)
    (hmem : ∀ x y, FormulaEdges s p v x y → s y x)
    (q : Formula (k + 2)) (w : Fin k → U)
    (hrefl : ∀ x, FormulaEdges s q w x x)
    (hpre : ∀ x y,
      ((∀ u, FormulaEdges s p v x u → ∃ v', FormulaEdges s p v y v' ∧ FormulaEdges s q w u v') ∧
       (∀ v', FormulaEdges s p v y v' → ∃ u, FormulaEdges s p v x u ∧ FormulaEdges s q w u v')) →
      FormulaEdges s q w x y) :
    ∀ x y, DefinedLeastRelation s p v x y → FormulaEdges s q w x y := by
  let C := definableMemberCover base p v hmem
  have hcode : ∀ i, ∃ r, GraphCode s (C.node i) r ∧
      ∀ x y, CodedRelation s r x y ↔ s x (C.node i) ∧ s y (C.node i) ∧ FormulaEdges s q w x y :=
    fun i => normalized_relation_comprehension base q w (C.node i)
  exact fun x y hxy => glued_least_minimal_locally_coded C (FormulaEdges s q w)
    hrefl hpre hcode x y ((defined_least_iff_glued base p v hmem x y).mp hxy)

def PrunedMember (s : U → U → Prop) (b x y : U) : Prop :=
  ¬s b x ∧ ¬s b y ∧ s y x

def prunedMemberFormula : Formula 3 :=
  .conj (.impl (.member 2 1) .bottom)
    (.conj (.impl (.member 2 0) .bottom) (.member 0 1))

theorem eval_prunedMemberFormula (b x y : U) :
    Eval s prunedMemberFormula (cons y (cons x (cons b Fin.elim0))) ↔ PrunedMember s b x y := by
  rfl

def PrunedLeastRelation (s : U → U → Prop) (b x y : U) : Prop :=
  DefinedLeastRelation s prunedMemberFormula (cons b Fin.elim0) x y

/-- This is the graph on the full carrier with excluded nodes having empty rows.
    It is not yet a quotient model or a proof that deleting those nodes preserves
    the construction. -/
theorem pruned_least_properties (base : BaseCollection s) (b : U) :
    Equivalence (PrunedLeastRelation s b) ∧
      ∀ x y, PrunedLeastRelation s b x y ↔
        (∀ u, PrunedMember s b x u → ∃ v, PrunedMember s b y v ∧ PrunedLeastRelation s b u v) ∧
        (∀ v, PrunedMember s b y v → ∃ u, PrunedMember s b x u ∧ PrunedLeastRelation s b u v) := by
  have hmem : ∀ x y, FormulaEdges s prunedMemberFormula (cons b Fin.elim0) x y → s y x :=
    fun _ _ h => h.2.2
  exact ⟨defined_least_equivalence base prunedMemberFormula (cons b Fin.elim0) hmem,
    defined_least_fixed base prunedMemberFormula (cons b Fin.elim0) hmem⟩

#print axioms defined_least_equivalence
#print axioms defined_least_fixed
#print axioms defined_least_minimal_definable
#print axioms pruned_least_properties
end FullBridge
