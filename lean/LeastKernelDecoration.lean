import InvolutionAmalgamGraph
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Fixed decoration with its least-relation kernel retained as an explicit
    verified conclusion, for descending graph symmetries. -/
theorem bafa_fixed_least_decoration (base : BaseCollection s) (hBAFA : BAFACode s)
    {t a e : U} (ht : TransitiveCode s t) (hG : GraphCode s a e)
    (hend : EndExtensionCode s a e t) :
    ∃ m g, LeastGraphRelationCode s a e m ∧ DecorationCode s a e g ∧
      (∀ x, s x t → CodedRelation s g x x) ∧
      (∀ x y v w, CodedRelation s g x v → CodedRelation s g y w →
        (v = w ↔ CodedRelation s m x y)) := by
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
  obtain ⟨T, f, _, hf, hfi, _, hfix⟩ := hBAFA t ht C E hEG hCExt hEnd
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
  refine ⟨m, g, hm, ⟨hgf, ?_⟩, ?_, ?_⟩
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
  · intro x y v w hxv hyw
    obtain ⟨hx, c, X, hc, hcX, hXv⟩ := (hg x v).mp hxv
    obtain ⟨hy, d, Y, hd, hdY, hYw⟩ := (hg y w).mp hyw
    constructor
    · intro hvw
      have hXY := hfi X Y v hXv (hvw.symm ▸ hYw)
      have hcd := class_label_injective base hfresh hcX (hXY.symm ▸ hdY)
      exact (least_graph_class_eq_iff base hG hm hx hy hc hd).mp hcd
    · intro hxy
      have hcd := (least_graph_class_eq_iff base hG hm hx hy hc hd).mpr hxy
      have hXY := huni c X Y hcX (hcd.symm ▸ hdY)
      exact coded_function_value_unique hf.1 hXv (hXY.symm ▸ hYw)

#print axioms bafa_fixed_least_decoration
end FullBridge
