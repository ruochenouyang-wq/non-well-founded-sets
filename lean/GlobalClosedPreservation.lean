import PrunedBaseModel
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The global relation preserves every internally bounded closed extensional
    part of the definable member-subgraph. -/
theorem defined_least_preserves_closed (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x) (c : U)
    (hc : ∀ x, s x c → ∀ y, FormulaEdges s p v x y → s y c)
    (he : ∀ x, s x c → ∀ y, s y c →
      (∀ z, s z c → (FormulaEdges s p v x z ↔ FormulaEdges s p v y z)) → x = y)
    {x y : U} (hx : s x c) (hy : s y c) (hxy : DefinedLeastRelation s p v x y) : x = y := by
  obtain ⟨d, hd, hcd⟩ := transitive_cover_exists base c
  let C := definableMemberCover base p v hmem
  let i : {d : U // TransitiveCode s d} := ⟨d, hd⟩
  have hci : GraphClosedCode s (C.node i) (C.edge i) c :=
    ⟨hcd, fun u hu z huz => hc u hu z ((C.edge_iff i u z).mp huz).2⟩
  have hei : GraphExtensionalCode s c (C.edge i) := by
    intro u hu z hz hrows
    apply he u hu z hz
    intro w hw
    exact ⟨fun h => ((C.edge_iff i z w).mp ((hrows w hw).mp
      ((C.edge_iff i u w).mpr ⟨hcd u hu, h⟩))).2,
      fun h => ((C.edge_iff i u w).mp ((hrows w hw).mpr
      ((C.edge_iff i z w).mpr ⟨hcd z hz, h⟩))).2⟩
  exact least_relation_preserves_closed_extensional base hci hei (C.minimal i) hx hy
    ((glued_least_local_iff base C i (hcd x hx) (hcd y hy)).mp
      ((defined_least_iff_glued base p v hmem x y).mp hxy))

theorem least_global_injective_on_closed (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x) (c : U)
    (hc : ∀ x, s x c → ∀ y, FormulaEdges s p v x y → s y c)
    (he : ∀ x, s x c → ∀ y, s y c →
      (∀ z, s z c → (FormulaEdges s p v x z ↔ FormulaEdges s p v y z)) → x = y)
    {x y : U} (hx : s x c) (hy : s y c) :
    leastGlobalCode base p v hmem x = leastGlobalCode base p v hmem y ↔ x = y :=
  ⟨fun h => defined_least_preserves_closed base p v hmem c hc he hx hy
    ((least_global_code_eq base p v hmem x y).mp h), fun h => congrArg _ h⟩

theorem least_global_reflects_closed_edges (base : BaseCollection s) {n} (p : Formula (n + 2))
    (v : Fin n → U) (hmem : ∀ x y, FormulaEdges s p v x y → s y x) (c : U)
    (hc : ∀ x, s x c → ∀ y, FormulaEdges s p v x y → s y c)
    (he : ∀ x, s x c → ∀ y, s y c →
      (∀ z, s z c → (FormulaEdges s p v x z ↔ FormulaEdges s p v y z)) → x = y)
    {x y : U} (hx : s x c) (hy : s y c) :
    leastGlobalMember base p v hmem (leastGlobalCode base p v hmem y)
      (leastGlobalCode base p v hmem x) ↔ FormulaEdges s p v x y := by
  constructor
  · intro h
    obtain ⟨z, hxz, hzq⟩ := (least_global_exact_members base p v hmem x _).mp h
    have hzy := (least_global_injective_on_closed base p v hmem c hc he (hc x hx z hxz) hy).mp hzq
    exact hzy ▸ hxz
  · intro h
    exact (least_global_exact_members base p v hmem x _).mpr ⟨y, h, rfl⟩

theorem pruned_transitive_parameter_preserved (base : BaseCollection s) {b t : U}
    (ht : TransitiveCode s t) (hg : ∀ x, s x t → ¬s b x) :
    ∀ x y, s x t → s y t →
      (prunedCode base b x = prunedCode base b y ↔ x = y) ∧
      (prunedMember base b (prunedCode base b y) (prunedCode base b x) ↔ s y x) := by
  have hc : ∀ x, s x t → ∀ y, FormulaEdges s prunedMemberFormula (cons b Fin.elim0) x y → s y t :=
    fun x hx y hxy => ht x hx y hxy.2.2
  have he : ∀ x, s x t → ∀ y, s y t →
      (∀ z, s z t → (FormulaEdges s prunedMemberFormula (cons b Fin.elim0) x z ↔
        FormulaEdges s prunedMemberFormula (cons b Fin.elim0) y z)) → x = y := by
    intro x hx y hy hrows
    apply base.extensional x y
    intro z
    constructor
    · intro hzx
      have hz := ht x hx z hzx
      exact ((hrows z hz).mp ⟨hg x hx, hg z hz, hzx⟩).2.2
    · intro hzy
      have hz := ht y hy z hzy
      exact ((hrows z hz).mpr ⟨hg y hy, hg z hz, hzy⟩).2.2
  intro x y hx hy
  refine ⟨least_global_injective_on_closed base prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) t hc he hx hy, ?_⟩
  exact (least_global_reflects_closed_edges base prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) t hc he hx hy).trans
    ⟨fun h => h.2.2, fun h => ⟨hg x hx, hg y hy, h⟩⟩

theorem pruned_transitive_parameter_image (base : BaseCollection s) {b t : U}
    (hbb : s b b) (ht : TransitiveCode s t) (hg : ∀ x, s x t → ¬s b x) :
    TransitiveCode (prunedMember base b) (prunedCode base b t) := by
  intro X hX Y hY
  obtain ⟨x, hx, rfl⟩ := ((pruned_good_row base hbb hg).2 X).mp hX
  obtain ⟨y, hy, rfl⟩ := (least_global_exact_members base prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) x Y).mp hY
  exact ((pruned_good_row base hbb hg).2 _).mpr ⟨y, ht x hx y hy.2.2, rfl⟩

#print axioms pruned_transitive_parameter_preserved
end FullBridge
