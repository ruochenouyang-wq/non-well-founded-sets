import LeastGraphRelation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def ClassLabel (s : U → U → Prop) (a m t tag c z : U) : Prop :=
  (s z t ∧ GraphClassCode s a m z c) ∨
  ((¬∃ x, s x t ∧ GraphClassCode s a m x c) ∧ IsOrderedPair s z tag c)

def classLabelFormula {n} (a m t tag c z : Fin n) : Formula n :=
  (Formula.conj (.member z t) (graphClassFormula c z a m)).disj
    (.conj (.impl (.ex (.conj (.member 0 t.succ)
      (graphClassFormula c.succ 0 a.succ m.succ))) .bottom)
      (orderedPairFormula z tag c))

theorem eval_classLabelFormula (s : U → U → Prop) {n}
    (a m t tag c z : Fin n) (v : Fin n → U) :
    Eval s (classLabelFormula a m t tag c z) v ↔
      ClassLabel s (v a) (v m) (v t) (v tag) (v c) (v z) := by
  simp only [classLabelFormula, eval_disj, Eval, eval_graphClassFormula,
    eval_orderedPairFormula, ClassLabel, cons_zero, cons_succ]

theorem class_label_total (base : BaseCollection s) (a m t tag c : U) :
    ∃ z, ClassLabel s a m t tag c z := by
  classical
  by_cases h : ∃ x, s x t ∧ GraphClassCode s a m x c
  · obtain ⟨x, hx⟩ := h
    exact ⟨x, Or.inl hx⟩
  · obtain ⟨z, hz⟩ := orderedPair_exists base.pairing tag c
    exact ⟨z, Or.inr ⟨h, hz⟩⟩

theorem class_label_unique (base : BaseCollection s) {a e m t tag c z w : U}
    (hG : GraphCode s a e) (hm : LeastGraphRelationCode s a e m)
    (ht : TransitiveCode s t) (hend : EndExtensionCode s a e t)
    (hz : ClassLabel s a m t tag c z) (hw : ClassLabel s a m t tag c w) : z = w := by
  rcases hz with hz | hz
  · rcases hw with hw | hw
    · exact (least_graph_quotient_preserves_parameter base hG hm ht hend hz.1 hw.1 hz.2 hw.2).mp rfl
    · exact False.elim (hw.1 ⟨z, hz⟩)
  · rcases hw with hw | hw
    · exact False.elim (hz.1 ⟨w, hw⟩)
    · exact orderedPair_unique base.extensional hz.2 hw.2

theorem class_label_injective (base : BaseCollection s) {a m t tag c d z : U}
    (hfresh : ∀ c z, IsOrderedPair s z tag c → ¬s z t)
    (hc : ClassLabel s a m t tag c z) (hd : ClassLabel s a m t tag d z) : c = d := by
  rcases hc with hc | hc
  · rcases hd with hd | hd
    · exact graph_class_unique base hc.2 hd.2
    · exact False.elim (hfresh d z hd.2 hc.1)
  · rcases hd with hd | hd
    · exact False.elim (hfresh c z hc.2 hd.1)
    · exact (orderedPair_injective hc.2 hd.2).2

theorem class_label_image (base : BaseCollection s) {a e m t : U}
    (hG : GraphCode s a e) (hm : LeastGraphRelationCode s a e m)
    (ht : TransitiveCode s t) (hend : EndExtensionCode s a e t) (b tag : U) :
    ∃ C, ∀ z, s z C ↔ ∃ c, s c b ∧ ClassLabel s a m t tag c z := by
  have hrep := collection_separation_replacement s base.collection base.separation
  obtain ⟨C, hC⟩ := hrep 4 (classLabelFormula 3 4 2 5 1 0)
    (cons t (cons a (cons m (cons tag Fin.elim0)))) b (by
      intro c _
      obtain ⟨z, hz⟩ := class_label_total base a m t tag c
      refine ⟨z, (eval_classLabelFormula s 3 4 2 5 1 0 _).mpr hz, ?_⟩
      intro w hw
      exact class_label_unique base hG hm ht hend
        ((eval_classLabelFormula s 3 4 2 5 1 0 _).mp hw) hz)
  refine ⟨C, ?_⟩
  intro z
  have h := hC z
  simp only [eval_classLabelFormula] at h
  exact h

def labeledEdgeFormula : Formula 8 :=
  .ex (.ex (.conj (.member 1 4) (.conj (.member 0 4)
    (.conj (classLabelFormula 6 7 8 9 1 3)
      (.conj (classLabelFormula 6 7 8 9 0 2) (relatedFormula 5 1 0))))))

theorem eval_labeledEdgeFormula (Y X b r a m t tag : U) :
    Eval s labeledEdgeFormula
      (cons Y (cons X (cons b (cons r (cons a (cons m (cons t (cons tag Fin.elim0)))))))) ↔
      ∃ c d, s c b ∧ s d b ∧ ClassLabel s a m t tag c X ∧
        ClassLabel s a m t tag d Y ∧ CodedRelation s r c d := by
  simp only [labeledEdgeFormula, Eval, eval_classLabelFormula, eval_relatedFormula]
  rfl

theorem labeled_graph_exists (base : BaseCollection s) {a m t tag b r C : U}
    (hC : ∀ z, s z C ↔ ∃ c, s c b ∧ ClassLabel s a m t tag c z) :
    ∃ E, GraphCode s C E ∧ ∀ X Y, CodedRelation s E X Y ↔
      ∃ c d, s c b ∧ s d b ∧ ClassLabel s a m t tag c X ∧
        ClassLabel s a m t tag d Y ∧ CodedRelation s r c d := by
  obtain ⟨E, hEG, hE⟩ := normalized_relation_comprehension base labeledEdgeFormula
    (cons b (cons r (cons a (cons m (cons t (cons tag Fin.elim0)))))) C
  refine ⟨E, hEG, ?_⟩
  intro X Y
  have h := hE X Y
  rw [eval_labeledEdgeFormula] at h
  constructor
  · intro hXY
    exact (h.mp hXY).2.2
  · rintro ⟨c, d, hc, hd, hcX, hdY, hcd⟩
    exact h.mpr ⟨(hC X).mpr ⟨c, hc, hcX⟩, (hC Y).mpr ⟨d, hd, hdY⟩,
      c, d, hc, hd, hcX, hdY, hcd⟩

theorem labeled_edge_at_classes (base : BaseCollection s) {a m t tag b r E c d X Y : U}
    (hfresh : ∀ c z, IsOrderedPair s z tag c → ¬s z t)
    (hE : ∀ X Y, CodedRelation s E X Y ↔ ∃ c d, s c b ∧ s d b ∧
      ClassLabel s a m t tag c X ∧ ClassLabel s a m t tag d Y ∧ CodedRelation s r c d)
    (hc : s c b) (hd : s d b) (hcX : ClassLabel s a m t tag c X)
    (hdY : ClassLabel s a m t tag d Y) : CodedRelation s E X Y ↔ CodedRelation s r c d := by
  constructor
  · intro hXY
    obtain ⟨c', d', _, _, hc', hd', hcd⟩ := (hE X Y).mp hXY
    have hcc := class_label_injective base hfresh hc' hcX
    have hdd := class_label_injective base hfresh hd' hdY
    subst c'
    subst d'
    exact hcd
  · intro hcd
    exact (hE X Y).mpr ⟨c, d, hc, hd, hcX, hdY, hcd⟩

def labeledPullbackFormula : Formula 7 :=
  .conj (.member 1 2) (.ex (.ex (.conj (graphClassFormula 1 3 4 5)
    (.conj (classLabelFormula 4 5 6 7 1 0) (relatedFormula 8 0 2)))))

theorem eval_labeledPullbackFormula (v x a m t tag f : U) :
    Eval s labeledPullbackFormula
      (cons v (cons x (cons a (cons m (cons t (cons tag (cons f Fin.elim0))))))) ↔
      s x a ∧ ∃ c z, GraphClassCode s a m x c ∧ ClassLabel s a m t tag c z ∧
        CodedRelation s f z v := by
  simp only [labeledPullbackFormula, Eval, eval_graphClassFormula,
    eval_classLabelFormula, eval_relatedFormula]
  rfl

theorem labeled_pullback_exists (base : BaseCollection s) (a m t tag f : U) :
    ∃ g, (∀ p, s p g → ∃ x y, s x a ∧ IsOrderedPair s p x y) ∧
      ∀ x v, CodedRelation s g x v ↔ s x a ∧
        ∃ c z, GraphClassCode s a m x c ∧ ClassLabel s a m t tag c z ∧ CodedRelation s f z v := by
  obtain ⟨d, hd⟩ := codedRelation_component_bound base.union f
  obtain ⟨D, hD⟩ := binary_union_exists base.pairing base.union a d
  obtain ⟨g, hg⟩ := relation_comprehension_members base labeledPullbackFormula
    (cons a (cons m (cons t (cons tag (cons f Fin.elim0))))) D
  refine ⟨g, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, v, _, _, hpxv, hev⟩ := (hg p).mp hp
    exact ⟨x, v, ((eval_labeledPullbackFormula v x a m t tag f).mp hev).1, hpxv⟩
  · intro x v
    constructor
    · rintro ⟨p, hp, hpxv⟩
      obtain ⟨x', v', _, _, hp', hev⟩ := (hg p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxv hp'
      exact (eval_labeledPullbackFormula v x a m t tag f).mp hev
    · rintro ⟨hx, c, z, hc, hcz, hzv⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x v
      exact ⟨p, (hg p).mpr ⟨x, v, (hD x).mpr (Or.inl hx),
        (hD v).mpr (Or.inr (hd z v hzv).2), hp,
        (eval_labeledPullbackFormula v x a m t tag f).mpr ⟨hx, c, z, hc, hcz, hzv⟩⟩, hp⟩

theorem bafa_fixed_graph_solvability (base : BaseCollection s)
    (hBAFA : BAFACode s) : FixedGraphSolvabilityCode s := by
  intro t ht a e hG hend
  obtain ⟨m, b, r, hm, hb, _, hr, hrext⟩ := least_extensional_graph_quotient_exists base hG
  obtain ⟨tag, hfresh⟩ := fresh_orderedPair_tag base t
  obtain ⟨C, hC⟩ := class_label_image base hG hm ht hend b tag
  obtain ⟨E, hEG, hE⟩ := labeled_graph_exists (r := r) base hC
  have huni : ∀ c X Y, ClassLabel s a m t tag c X →
      ClassLabel s a m t tag c Y → X = Y := fun _ _ _ => class_label_unique base hG hm ht hend
  have hrep : ∀ c d X Y, s c b → s d b → ClassLabel s a m t tag c X →
      ClassLabel s a m t tag d Y → (CodedRelation s E X Y ↔ CodedRelation s r c d) :=
    fun _ _ _ _ => labeled_edge_at_classes base hfresh hE
  have hCt : Subset s t C := by
    intro x hx
    obtain ⟨c, hc⟩ := graph_class_exists base a m x
    exact (hC x).mpr ⟨c, (hb c).mpr ⟨x, hend.1 x hx, hc⟩, Or.inl ⟨hx, hc⟩⟩
  have hCExt : GraphExtensionalCode s C E := by
    intro X hX Y hY hrows
    obtain ⟨c, hc, hcX⟩ := (hC X).mp hX
    obtain ⟨d, hd, hdY⟩ := (hC Y).mp hY
    have hcd : c = d := by
      apply hrext c hc d hd
      intro k hk
      obtain ⟨Z, hkZ⟩ := class_label_total base a m t tag k
      have hZ := (hC Z).mpr ⟨k, hk, hkZ⟩
      exact (hrep c k X Z hc hk hcX hkZ).symm.trans
        ((hrows Z hZ).trans (hrep d k Y Z hd hk hdY hkZ))
    subst d
    exact huni c X Y hcX hdY
  have hEnd : EndExtensionCode s C E t := by
    refine ⟨hCt, ?_⟩
    intro x hx Y
    obtain ⟨c, hc⟩ := graph_class_exists base a m x
    have hcb := (hb c).mpr ⟨x, hend.1 x hx, hc⟩
    have hcx : ClassLabel s a m t tag c x := Or.inl ⟨hx, hc⟩
    constructor
    · intro hxY
      obtain ⟨c', d, _, hd, hc'x, hdY, hrc'd⟩ := (hE x Y).mp hxY
      have hcc := class_label_injective base hfresh hc'x hcx
      subst c'
      obtain ⟨y, _, hexy, hdy⟩ :=
        (least_graph_quotient_edge_from_representative base hG hm (hend.1 x hx) hc).mp
          ((hr c d).mp hrc'd)
      have hyx := (hend.2 x hx y).mp hexy
      have hyt := ht x hx y hyx
      have hYy := huni d Y y hdY (Or.inl ⟨hyt, hdy⟩)
      exact hYy.symm ▸ hyx
    · intro hYx
      have hYt := ht x hx Y hYx
      obtain ⟨d, hd⟩ := graph_class_exists base a m Y
      exact (hE x Y).mpr ⟨c, d, hcb, (hb d).mpr ⟨Y, hend.1 Y hYt, hd⟩,
        hcx, Or.inl ⟨hYt, hd⟩, (hr c d).mpr
          ⟨x, Y, hend.1 x hx, hend.1 Y hYt, hc, hd, (hend.2 x hx Y).mpr hYx⟩⟩
  obtain ⟨T, f, _, hf, _, _, hfix⟩ := hBAFA t ht C E hEG hCExt hEnd
  obtain ⟨g, hgn, hg⟩ := labeled_pullback_exists base a m t tag f
  have hgf : FunctionCode s a g := by
    refine ⟨hgn, ?_⟩
    intro x hx
    obtain ⟨c, hc⟩ := graph_class_exists base a m x
    obtain ⟨X, hcX⟩ := class_label_total base a m t tag c
    have hX := (hC X).mpr ⟨c, (hb c).mpr ⟨x, hx, hc⟩, hcX⟩
    obtain ⟨v, hXv, hu⟩ := hf.1.2 X hX
    refine ⟨v, (hg x v).mpr ⟨hx, c, X, hc, hcX, hXv⟩, ?_⟩
    intro w hxw
    obtain ⟨_, c', Y, hc', hcY, hYw⟩ := (hg x w).mp hxw
    have hcc := graph_class_unique base hc' hc
    subst c'
    have hYX := huni c Y X hcY hcX
    subst Y
    exact hu w hYw
  refine ⟨g, ⟨hgf, ?_⟩, ?_⟩
  · intro x hx v hxv w
    obtain ⟨_, c, X, hc, hcX, hXv⟩ := (hg x v).mp hxv
    have hcb := (hb c).mpr ⟨x, hx, hc⟩
    have hXC := (hC X).mpr ⟨c, hcb, hcX⟩
    constructor
    · intro hwv
      obtain ⟨Y, hYC, hEXY, hYw⟩ := (hf.2 X hXC v hXv w).mp hwv
      obtain ⟨d, hdb, hdY⟩ := (hC Y).mp hYC
      have hrcd := (hrep c d X Y hcb hdb hcX hdY).mp hEXY
      obtain ⟨y, hy, hexy, hdy⟩ :=
        (least_graph_quotient_edge_from_representative base hG hm hx hc).mp ((hr c d).mp hrcd)
      exact ⟨y, hy, hexy, (hg y w).mpr ⟨hy, d, Y, hdy, hdY, hYw⟩⟩
    · rintro ⟨y, hy, hexy, hgyw⟩
      obtain ⟨_, d, Y, hd, hdY, hYw⟩ := (hg y w).mp hgyw
      have hdb := (hb d).mpr ⟨y, hy, hd⟩
      have hYC := (hC Y).mpr ⟨d, hdb, hdY⟩
      have hrcd := (hr c d).mpr ⟨x, y, hx, hy, hc, hd, hexy⟩
      exact (hf.2 X hXC v hXv w).mpr
        ⟨Y, hYC, (hrep c d X Y hcb hdb hcX hdY).mpr hrcd, hYw⟩
  · intro x hx
    obtain ⟨c, hc⟩ := graph_class_exists base a m x
    exact (hg x x).mpr ⟨hend.1 x hx, c, x, hc, Or.inl ⟨hx, hc⟩, hfix x hx⟩

def BafaModel.toFixed (M : BafaModel.{u}) : FixedSolvableModel.{u} where
  Carrier := M.Carrier
  mem := M.mem
  base := M.base
  fixedSolvability := bafa_fixed_graph_solvability M.base M.boffa

theorem bafa_quotient_factors_through_fixed (M : BafaModel.{u}) :
    M.toFixed.behaviorQuotient = M.behaviorQuotient := by
  rfl

#print axioms bafa_fixed_graph_solvability
#print axioms bafa_quotient_factors_through_fixed
end FullBridge
