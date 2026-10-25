import ClosedMapConservation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Keeps all relevant retained representatives inside one actual transitive
    source bound; it does not choose one representative per target object. -/
structure PrunedFixedCover (base : BaseCollection s) (b : U) (T : PrunedQuotient base b) where
  surrounding : U
  transitive : TransitiveCode s surrounding
  carrier : U
  members_iff : ∀ x, s x carrier ↔ s x surrounding ∧ ¬s b x ∧ prunedMember base b (prunedCode base b x) T
  image : prunedCode base b carrier = T
  closed : ∀ x, s x carrier → ∀ y, PrunedMember s b x y → s y carrier

theorem pruned_fixed_cover_exists (base : BaseCollection s) {b : U} (hbb : s b b)
    (T : PrunedQuotient base b) (hT : TransitiveCode (prunedMember base b) T) :
    Nonempty (PrunedFixedCover base b T) := by
  obtain ⟨a, hag, hqa⟩ := pruned_clean_representative base hbb T
  obtain ⟨d, hdt, had⟩ := transitive_cover_exists base a
  obtain ⟨c, hc⟩ := base.separation 2
    (.conj (.impl (.member 2 0) .bottom) (leastGlobalMemberFormula prunedMemberFormula))
    (cons a (cons b Fin.elim0)) d
  have hc' : ∀ x, s x c ↔ s x d ∧ ¬s b x ∧ prunedMember base b (prunedCode base b x) T := by
    intro x
    have h := hc x
    simp only [Eval, eval_leastGlobalMemberFormula base prunedMemberFormula
      (cons b Fin.elim0) (pruned_edges_are_members b)] at h
    change s x c ↔ s x d ∧ ¬s b x ∧ prunedMember base b (prunedCode base b x) (prunedCode base b a) at h
    simpa only [hqa] using h
  have hcg : ∀ x, s x c → ¬s b x := fun x hx => ((hc' x).mp hx).2.1
  have hqc : prunedCode base b c = T := by
    apply least_global_extensional base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b)
    intro X
    constructor
    · intro hX
      obtain ⟨x, hx, rfl⟩ := ((pruned_good_row base hbb hcg).2 X).mp hX
      exact ((hc' x).mp hx).2.2
    · intro hX
      have hXa : prunedMember base b X (prunedCode base b a) := hqa.symm ▸ hX
      obtain ⟨x, hx, rfl⟩ := ((pruned_good_row base hbb hag).2 X).mp hXa
      exact ((pruned_good_row base hbb hcg).2 _).mpr ⟨x, (hc' x).mpr ⟨had x hx, hag x hx, hX⟩, rfl⟩
  refine ⟨⟨d, hdt, c, hc', hqc, ?_⟩⟩
  intro x hx y hxy
  obtain ⟨hxd, _, hqxT⟩ := (hc' x).mp hx
  have hqyqx := (least_global_exact_members base prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) x (prunedCode base b y)).mpr ⟨y, hxy, rfl⟩
  exact (hc' y).mpr ⟨hdt x hxd y hxy.2.2, hxy.2.1, hT _ hqxT _ hqyqx⟩

def prunedEqualAtFormula {n} (b x y : Fin n) : Formula n :=
  Formula.translateParameters (leastGlobalEqualFormula prunedMemberFormula)
    (leastGlobalMemberFormula prunedMemberFormula) (fun _ => b) id (.equal x y)

theorem eval_prunedEqualAtFormula (base : BaseCollection s) {n} (b x y : Fin n) (e : Fin n → U) :
    Eval s (prunedEqualAtFormula b x y) e ↔ prunedCode base (e b) (e x) = prunedCode base (e b) (e y) :=
  least_global_formula_translation base prunedMemberFormula (cons (e b) Fin.elim0)
    (pruned_edges_are_members (e b)) (.equal x y) (fun _ => b) id e
    (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j)

/-- Free variables: [class, object, carrier, representatives, relation, b]. -/
def prunedClassificationFormula : Formula 6 :=
  .conj (.member 1 2) (.ex (.conj (.member 0 4)
    (.conj (graphClassFormula 1 0 4 5) (prunedEqualAtFormula 6 2 0))))

theorem eval_prunedClassificationFormula (base : BaseCollection s) {b : U} {A : PrunedQuotient base b}
    (P : PrunedNodePresentation base b A) (S x c : U) :
    Eval s prunedClassificationFormula
      (cons c (cons x (cons S (cons P.representatives (cons P.relation (cons b Fin.elim0)))))) ↔
      s x S ∧ PrunedNodeCorresponds P c (prunedCode base b x) := by
  simp only [prunedClassificationFormula, Eval, eval_graphClassFormula, eval_prunedEqualAtFormula base]
  change (s x S ∧ ∃ y, s y P.representatives ∧ GraphClassCode s P.representatives P.relation y c ∧
    prunedCode base b x = prunedCode base b y) ↔ _
  exact and_congr_right (fun _ => ⟨fun ⟨y, hy, hc, hq⟩ => ⟨y, hy, hc, hq.symm⟩,
    fun ⟨y, hy, hc, hq⟩ => ⟨y, hy, hc, hq.symm⟩⟩)

theorem pruned_classification_exists (base : BaseCollection s) {b : U} (hbb : s b b)
    {A : PrunedQuotient base b} (P : PrunedNodePresentation base b A) (S : U)
    (hSA : ∀ x, s x S → prunedMember base b (prunedCode base b x) A) :
    ∃ h, FunctionCode s S h ∧ ∀ x c, CodedRelation s h x c ↔
      s x S ∧ PrunedNodeCorresponds P c (prunedCode base b x) := by
  obtain ⟨u, hu⟩ := binary_union_exists base.pairing base.union S P.nodes
  obtain ⟨h, hhmem⟩ := relation_comprehension_members base prunedClassificationFormula
    (cons S (cons P.representatives (cons P.relation (cons b Fin.elim0)))) u
  have hh : ∀ x c, CodedRelation s h x c ↔ s x S ∧ PrunedNodeCorresponds P c (prunedCode base b x) := by
    intro x c
    constructor
    · rintro ⟨v, hv, hvxc⟩
      obtain ⟨x', c', _, _, hp, hev⟩ := (hhmem v).mp hv
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hvxc hp
      exact (eval_prunedClassificationFormula base P S x c).mp hev
    · rintro ⟨hx, hc⟩
      have hcnode : s c P.nodes := by
        obtain ⟨y, hy, hyc, _⟩ := hc
        exact (P.nodes_iff c).mpr ⟨y, hy, hyc⟩
      obtain ⟨v, hv⟩ := orderedPair_exists base.pairing x c
      exact ⟨v, (hhmem v).mpr ⟨x, c, (hu x).mpr (Or.inl hx), (hu c).mpr (Or.inr hcnode), hv,
        (eval_prunedClassificationFormula base P S x c).mpr ⟨hx, hc⟩⟩, hv⟩
  refine ⟨h, ⟨?_, ?_⟩, hh⟩
  · intro v hv
    obtain ⟨x, c, _, _, hpair, hev⟩ := (hhmem v).mp hv
    exact ⟨x, c, ((eval_prunedClassificationFormula base P S x c).mp hev).1, hpair⟩
  · intro x hx
    obtain ⟨c, _, hc⟩ := (pruned_node_correspondence_total base hbb P).2 _ (hSA x hx)
    refine ⟨c, (hh x c).mpr ⟨hx, hc⟩, ?_⟩
    intro d hd
    exact (pruned_node_correspondence_eq base P ((hh x d).mp hd).2 hc).mpr rfl

theorem pruned_classification_kernel (base : BaseCollection s) {b : U} {A : PrunedQuotient base b}
    (P : PrunedNodePresentation base b A) {S h : U}
    (hh : ∀ x c, CodedRelation s h x c ↔ s x S ∧ PrunedNodeCorresponds P c (prunedCode base b x))
    {x y c d : U} (hxc : CodedRelation s h x c) (hyd : CodedRelation s h y d) :
    c = d ↔ prunedCode base b x = prunedCode base b y :=
  pruned_node_correspondence_eq base P ((hh x c).mp hxc).2 ((hh y d).mp hyd).2

theorem pruned_fixed_classification_rows (base : BaseCollection s) {b : U} (hbb : s b b)
    {T A R : PrunedQuotient base b} (C : PrunedFixedCover base b T)
    (P : PrunedNodePresentation base b A) {e h : U}
    (he : ∀ c d X Y, PrunedNodeCorresponds P c X → PrunedNodeCorresponds P d Y →
      (CodedRelation s e c d ↔ CodedRelation (prunedMember base b) R X Y))
    (hend : EndExtensionCode (prunedMember base b) A R T)
    (hh : ∀ x c, CodedRelation s h x c ↔ s x C.carrier ∧ PrunedNodeCorresponds P c (prunedCode base b x)) :
    ∀ x c, s x C.carrier → CodedRelation s h x c → ∀ d, s d P.nodes →
      (CodedRelation s e c d ↔ ∃ y, PrunedMember s b x y ∧ CodedRelation s h y d) := by
  intro x c hx hxc d hd
  have hcX := ((hh x c).mp hxc).2
  have hXT := ((C.members_iff x).mp hx).2.2
  constructor
  · intro hcd
    obtain ⟨Y, _, hdY⟩ := (pruned_node_correspondence_total base hbb P).1 d hd
    have hXY := (he c d _ Y hcX hdY).mp hcd
    have hYX := (hend.2 _ hXT Y).mp hXY
    obtain ⟨y, hxy, hqy⟩ := (least_global_exact_members base prunedMemberFormula (cons b Fin.elim0)
      (pruned_edges_are_members b) x Y).mp hYX
    refine ⟨y, hxy, (hh y d).mpr ⟨C.closed x hx y hxy, ?_⟩⟩
    simpa only [hqy] using hdY
  · rintro ⟨y, hxy, hyd⟩
    have hdY := ((hh y d).mp hyd).2
    apply (he c d _ _ hcX hdY).mpr
    apply (hend.2 _ hXT _).mpr
    exact (least_global_exact_members base prunedMemberFormula (cons b Fin.elim0)
      (pruned_edges_are_members b) x _).mpr ⟨y, hxy, rfl⟩

/-- The fixed-side cover and classification map are constructed, not assumed. -/
theorem pruned_fixed_cover_classification (base : BaseCollection s) {b : U} (hbb : s b b)
    {T A R : PrunedQuotient base b} (hT : TransitiveCode (prunedMember base b) T)
    (P : PrunedNodePresentation base b A) {e : U}
    (he : ∀ c d X Y, PrunedNodeCorresponds P c X → PrunedNodeCorresponds P d Y →
      (CodedRelation s e c d ↔ CodedRelation (prunedMember base b) R X Y))
    (hend : EndExtensionCode (prunedMember base b) A R T) :
    ∃ C : PrunedFixedCover base b T, ∃ h, FunctionCode s C.carrier h ∧
      (∀ x c, CodedRelation s h x c ↔ s x C.carrier ∧ PrunedNodeCorresponds P c (prunedCode base b x)) ∧
      ∀ x c, s x C.carrier → CodedRelation s h x c → ∀ d, s d P.nodes →
        (CodedRelation s e c d ↔ ∃ y, PrunedMember s b x y ∧ CodedRelation s h y d) := by
  obtain ⟨C⟩ := pruned_fixed_cover_exists base hbb T hT
  obtain ⟨h, hf, hh⟩ := pruned_classification_exists base hbb P C.carrier
    (fun x hx => hend.1 _ ((C.members_iff x).mp hx).2.2)
  exact ⟨C, h, hf, hh, pruned_fixed_classification_rows base hbb C P he hend hh⟩

#print axioms pruned_fixed_cover_classification
end FullBridge
