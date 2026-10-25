import BafaModelObstructions
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

theorem closed_induced_graph_exists (base : BaseCollection s) (c e : U) :
    ∃ f, GraphCode s c f ∧ ∀ x y, CodedRelation s f x y ↔
      s x c ∧ s y c ∧ CodedRelation s e x y := by
  obtain ⟨f, hfG, hf⟩ := normalized_relation_comprehension base
    (relatedFormula (n := 3) 2 1 0) (cons e Fin.elim0) c
  refine ⟨f, hfG, ?_⟩
  intro x y
  exact (hf x y).trans (and_congr_right (fun _ => and_congr_right
    (fun _ => eval_relatedFormula s 2 1 0 _)))

/-- Exact restriction, without assuming the closed subgraph is extensional. -/
theorem least_relation_closed_restriction (base : BaseCollection s)
    {a e c f m n : U} (hc : GraphClosedCode s a e c)
    (hf : ∀ x y, CodedRelation s f x y ↔ s x c ∧ s y c ∧ CodedRelation s e x y)
    (hm : LeastGraphRelationCode s a e m) (hn : LeastGraphRelationCode s c f n)
    {x y : U} (hx : s x c) (hy : s y c) :
    CodedRelation s m x y ↔ CodedRelation s n x y := by
  constructor
  · intro hxy
    obtain ⟨k, hkG, hk⟩ := normalized_relation_comprehension base
      (.impl (.conj (.member 1 2) (.member 0 2)) (relatedFormula 3 1 0))
      (cons c (cons n Fin.elim0)) a
    have hi : ∀ u v, CodedRelation s k u v ↔ s u a ∧ s v a ∧
        (s u c ∧ s v c → CodedRelation s n u v) := by
      intro u v
      have h := hk u v
      simp only [Eval, eval_relatedFormula] at h
      exact h
    have hkp : GraphPreFixedCode s a e k := by
      refine ⟨hkG, fun u hu => (hi u u).mpr
        ⟨hu, hu, fun h => hn.1.2.1 u h.1⟩, ?_⟩
      intro u v hu hv hmatch
      refine (hi u v).mpr ⟨hu, hv, ?_⟩
      rintro ⟨huc, hvc⟩
      apply hn.1.2.2 u v huc hvc
      constructor
      · intro z huz
        have huzE := ((hf u z).mp huz).2.2
        obtain ⟨w, hvw, hzw⟩ := hmatch.1 z huzE
        have hzc := hc.2 u huc z huzE
        have hwc := hc.2 v hvc w hvw
        exact ⟨w, (hf v w).mpr ⟨hvc, hwc, hvw⟩,
          ((hi z w).mp hzw).2.2 ⟨hzc, hwc⟩⟩
      · intro w hvw
        have hvwE := ((hf v w).mp hvw).2.2
        obtain ⟨z, huz, hzw⟩ := hmatch.2 w hvwE
        have hzc := hc.2 u huc z huz
        have hwc := hc.2 v hvc w hvwE
        exact ⟨z, (hf u z).mpr ⟨huc, hzc, huz⟩,
          ((hi z w).mp hzw).2.2 ⟨hzc, hwc⟩⟩
    exact ((hi x y).mp (hm.2 k hkp x y hxy)).2.2 ⟨hx, hy⟩
  · intro hxy
    obtain ⟨k, hkG, hk⟩ := closed_induced_graph_exists base c m
    have hkp : GraphPreFixedCode s c f k := by
      refine ⟨hkG, fun u hu => (hk u u).mpr ⟨hu, hu, hm.1.2.1 u (hc.1 u hu)⟩, ?_⟩
      intro u v hu hv hmatch
      refine (hk u v).mpr ⟨hu, hv, hm.1.2.2 u v (hc.1 u hu) (hc.1 v hv) ?_⟩
      constructor
      · intro z huz
        obtain ⟨w, hvw, hzw⟩ := hmatch.1 z ((hf u z).mpr ⟨hu, hc.2 u hu z huz, huz⟩)
        exact ⟨w, ((hf v w).mp hvw).2.2, ((hk z w).mp hzw).2.2⟩
      · intro w hvw
        obtain ⟨z, huz, hzw⟩ := hmatch.2 w ((hf v w).mpr ⟨hv, hc.2 v hv w hvw, hvw⟩)
        exact ⟨z, ((hf u z).mp huz).2.2, ((hk z w).mp hzw).2.2⟩
    exact ((hk x y).mp (hn.2 k hkp x y hxy)).2.2

/-- Given cover data, not an assertion that such an internal cover has been
    constructed for an arbitrary class graph. All edges and local relations are
    actual source codes; indices and the ambient relation are external. -/
structure ClosedLeastCover (s : U → U → Prop) (E : U → U → Prop) (I : Type v) where
  node : I → U
  edge : I → U
  least : I → U
  covers : ∀ x, ∃ i, s x (node i)
  directed : ∀ i j, ∃ k, Subset s (node i) (node k) ∧ Subset s (node j) (node k)
  closed : ∀ i x, s x (node i) → ∀ y, E x y → s y (node i)
  graph : ∀ i, GraphCode s (node i) (edge i)
  edge_iff : ∀ i x y, CodedRelation s (edge i) x y ↔ s x (node i) ∧ E x y
  minimal : ∀ i, LeastGraphRelationCode s (node i) (edge i) (least i)

noncomputable def ClosedLeastCover.fromGraphs (base : BaseCollection s)
    {E : U → U → Prop} {I : Type v} (node edge : I → U)
    (covers : ∀ x, ∃ i, s x (node i))
    (directed : ∀ i j, ∃ k, Subset s (node i) (node k) ∧ Subset s (node j) (node k))
    (closed : ∀ i x, s x (node i) → ∀ y, E x y → s y (node i))
    (graph : ∀ i, GraphCode s (node i) (edge i))
    (edge_iff : ∀ i x y, CodedRelation s (edge i) x y ↔ s x (node i) ∧ E x y) :
    ClosedLeastCover s E I where
  node := node
  edge := edge
  least := fun i => Classical.choose (least_graph_relation_exists base (node i) (edge i))
  covers := covers
  directed := directed
  closed := closed
  graph := graph
  edge_iff := edge_iff
  minimal := fun i => Classical.choose_spec (least_graph_relation_exists base (node i) (edge i))

def GluedLeastRelation {E : U → U → Prop} {I : Type v}
    (C : ClosedLeastCover s E I) (x y : U) : Prop :=
  ∃ i, s x (C.node i) ∧ s y (C.node i) ∧ CodedRelation s (C.least i) x y

theorem cover_least_restriction (base : BaseCollection s) {E : U → U → Prop}
    {I : Type v} (C : ClosedLeastCover s E I) {i j : I}
    (hij : Subset s (C.node i) (C.node j)) {x y : U}
    (hx : s x (C.node i)) (hy : s y (C.node i)) :
    CodedRelation s (C.least j) x y ↔ CodedRelation s (C.least i) x y := by
  apply least_relation_closed_restriction base (a := C.node j) (e := C.edge j)
    (c := C.node i) (f := C.edge i) ?_ ?_ (C.minimal j) (C.minimal i) hx hy
  · exact ⟨hij, fun u hu v huv => C.closed i u hu v ((C.edge_iff j u v).mp huv).2⟩
  · intro u v
    rw [C.edge_iff i u v, C.edge_iff j u v]
    exact ⟨fun h => ⟨h.1, C.closed i u h.1 v h.2, hij u h.1, h.2⟩,
      fun h => ⟨h.1, h.2.2.2⟩⟩

theorem glued_least_local_iff (base : BaseCollection s) {E : U → U → Prop}
    {I : Type v} (C : ClosedLeastCover s E I) (i : I) {x y : U}
    (hx : s x (C.node i)) (hy : s y (C.node i)) :
    GluedLeastRelation C x y ↔ CodedRelation s (C.least i) x y := by
  constructor
  · rintro ⟨j, hxj, hyj, hxy⟩
    obtain ⟨k, hik, hjk⟩ := C.directed i j
    exact (cover_least_restriction base C hik hx hy).mp
      ((cover_least_restriction base C hjk hxj hyj).mpr hxy)
  · exact fun h => ⟨i, hx, hy, h⟩

theorem glued_least_equivalence (base : BaseCollection s) {E : U → U → Prop}
    {I : Type v} (C : ClosedLeastCover s E I) : Equivalence (GluedLeastRelation C) := by
  constructor
  · intro x
    obtain ⟨i, hx⟩ := C.covers x
    exact ⟨i, hx, hx, (C.minimal i).1.2.1 x hx⟩
  · intro x y hxy
    obtain ⟨i, hx, hy, hxy⟩ := hxy
    exact ⟨i, hy, hx, least_graph_relation_symm base (C.minimal i) hxy⟩
  · intro x y z hxy hyz
    obtain ⟨i, hxi, hyi, hxy⟩ := hxy
    obtain ⟨j, hyj, hzj, hyz⟩ := hyz
    obtain ⟨k, hik, hjk⟩ := C.directed i j
    exact ⟨k, hik x hxi, hjk z hzj, least_graph_relation_trans base (C.graph k) (C.minimal k)
      ((cover_least_restriction base C hik hxi hyi).mpr hxy)
      ((cover_least_restriction base C hjk hyj hzj).mpr hyz)⟩

theorem glued_least_fixed (base : BaseCollection s) {E : U → U → Prop}
    {I : Type v} (C : ClosedLeastCover s E I) (x y : U) :
    GluedLeastRelation C x y ↔
      (∀ u, E x u → ∃ v, E y v ∧ GluedLeastRelation C u v) ∧
      (∀ v, E y v → ∃ u, E x u ∧ GluedLeastRelation C u v) := by
  obtain ⟨i, hxi⟩ := C.covers x
  obtain ⟨j, hyj⟩ := C.covers y
  obtain ⟨k, hik, hjk⟩ := C.directed i j
  have hx := hik x hxi
  have hy := hjk y hyj
  rw [glued_least_local_iff base C k hx hy,
    least_graph_relation_fixed base (C.graph k) (C.minimal k)]
  constructor
  · rintro ⟨_, _, hmatch⟩
    constructor
    · intro u hxu
      obtain ⟨v, hyv, huv⟩ := hmatch.1 u ((C.edge_iff k x u).mpr ⟨hx, hxu⟩)
      have hyvE := ((C.edge_iff k y v).mp hyv).2
      exact ⟨v, hyvE, (glued_least_local_iff base C k
        (C.closed k x hx u hxu) (C.closed k y hy v hyvE)).mpr huv⟩
    · intro v hyv
      obtain ⟨u, hxu, huv⟩ := hmatch.2 v ((C.edge_iff k y v).mpr ⟨hy, hyv⟩)
      have hxuE := ((C.edge_iff k x u).mp hxu).2
      exact ⟨u, hxuE, (glued_least_local_iff base C k
        (C.closed k x hx u hxuE) (C.closed k y hy v hyv)).mpr huv⟩
  · rintro ⟨hforward, hback⟩
    refine ⟨hx, hy, ?_, ?_⟩
    · intro u hxu
      have hxuE := ((C.edge_iff k x u).mp hxu).2
      obtain ⟨v, hyv, huv⟩ := hforward u hxuE
      exact ⟨v, (C.edge_iff k y v).mpr ⟨hy, hyv⟩,
        (glued_least_local_iff base C k (C.closed k x hx u hxuE)
          (C.closed k y hy v hyv)).mp huv⟩
    · intro v hyv
      have hyvE := ((C.edge_iff k y v).mp hyv).2
      obtain ⟨u, hxu, huv⟩ := hback v hyvE
      exact ⟨u, (C.edge_iff k x u).mpr ⟨hx, hxu⟩,
        (glued_least_local_iff base C k (C.closed k x hx u hxu)
          (C.closed k y hy v hyvE)).mp huv⟩

/-- Minimality is asserted only against external pre-fixed relations whose local
    restrictions have actual internal codes. Arbitrary external comprehension is
    not available from the source separation scheme. -/
theorem glued_least_minimal_locally_coded
    {E : U → U → Prop} {I : Type v} (C : ClosedLeastCover s E I)
    (K : U → U → Prop) (hrefl : ∀ x, K x x)
    (hpre : ∀ x y,
      ((∀ u, E x u → ∃ v, E y v ∧ K u v) ∧
       (∀ v, E y v → ∃ u, E x u ∧ K u v)) → K x y)
    (hcode : ∀ i, ∃ r, GraphCode s (C.node i) r ∧
      ∀ x y, CodedRelation s r x y ↔ s x (C.node i) ∧ s y (C.node i) ∧ K x y) :
    ∀ x y, GluedLeastRelation C x y → K x y := by
  intro x y hxy
  obtain ⟨i, _, _, hxy⟩ := hxy
  obtain ⟨r, hrG, hr⟩ := hcode i
  have hrP : GraphPreFixedCode s (C.node i) (C.edge i) r := by
    refine ⟨hrG, fun u hu => (hr u u).mpr ⟨hu, hu, hrefl u⟩, ?_⟩
    intro u v hu hv hmatch
    refine (hr u v).mpr ⟨hu, hv, hpre u v ?_⟩
    constructor
    · intro z huz
      obtain ⟨w, hvw, hzw⟩ := hmatch.1 z ((C.edge_iff i u z).mpr ⟨hu, huz⟩)
      exact ⟨w, ((C.edge_iff i v w).mp hvw).2, ((hr z w).mp hzw).2.2⟩
    · intro w hvw
      obtain ⟨z, huz, hzw⟩ := hmatch.2 w ((C.edge_iff i v w).mpr ⟨hv, hvw⟩)
      exact ⟨z, ((C.edge_iff i u z).mp huz).2, ((hr z w).mp hzw).2.2⟩
  exact ((hr x y).mp ((C.minimal i).2 r hrP x y hxy)).2.2

#print axioms glued_least_fixed
#print axioms glued_least_minimal_locally_coded
end FullBridge
