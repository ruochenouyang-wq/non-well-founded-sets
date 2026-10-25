import PrunedEvaluationKernel
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- AFA uniqueness implies internal strong extensionality on every actual
    transitive set, by solving its internally coded maximal-bisimulation quotient. -/
theorem afa_transitive_internal_strong_extensional (base : BaseCollection s) (hA : AFACode s)
    {a : U} (ha : TransitiveCode s a) : InternallyStrongExtensional s a := by
  intro r hrG hrB x y hxy
  obtain ⟨e, i, hG, hi, he, hir⟩ := membership_graph_identity_decoration base ha
  obtain ⟨m, hm⟩ := maximal_graph_bisim_exists base a e
  have hrGB : GraphBisimCode s a e r := by
    refine ⟨hrG, ?_⟩
    intro u v huv
    have hb := graphCode_endpoints hrG huv
    constructor
    · intro z huz
      obtain ⟨w, hwv, hzw⟩ := (hrB u v huv).1 z ((he u z).mp huz).2
      exact ⟨w, (he v w).mpr ⟨hb.2, hwv⟩, hzw⟩
    · intro w hvw
      obtain ⟨z, hzu, hzw⟩ := (hrB u v huv).2 w ((he v w).mp hvw).2
      exact ⟨z, (he u z).mpr ⟨hb.1, hzu⟩, hzw⟩
  have hmxy := hm.2 r hrGB x y hxy
  have hEnds := graphCode_endpoints hrG hxy
  obtain ⟨B, hB⟩ := graph_class_nodes_exists base a m
  obtain ⟨R, hRG, hR⟩ := graph_quotient_edges_exists base e hB
  obtain ⟨f, hf, _⟩ := hA B R hRG
  obtain ⟨g, hgp, hg⟩ := graph_class_pullback_exists base a m f
  have hgDec := graph_class_pullback_decoration base hG hm hB hR hf hgp hg
  obtain ⟨k, _, hku⟩ := hA a e hG
  have hgi : g = i := (hku g hgDec).trans (hku i hi).symm
  obtain ⟨c, hxc⟩ := graph_class_exists base a m x
  obtain ⟨d, hyd⟩ := graph_class_exists base a m y
  have hcd := (graph_class_eq_iff base hG hm hEnds.1 hEnds.2 hxc hyd).mpr hmxy
  obtain ⟨v, hcv, _⟩ := hf.1.2 c ((hB c).mpr ⟨x, hEnds.1, hxc⟩)
  have hxv := (hg x v).mpr ⟨hEnds.1, c, hxc, hcv⟩
  have hyv := (hg y v).mpr ⟨hEnds.2, d, hyd, hcd ▸ hcv⟩
  exact (((hir x v).mp (hgi ▸ hxv)).2).symm.trans (((hir y v).mp (hgi ▸ hyv)).2)

theorem afa_internal_behavior_iff_equal (base : BaseCollection s) (hA : AFACode s) (x y : U) :
    InternalBehavior s x y ↔ x = y := by
  constructor
  · rintro ⟨r, hr, hxy⟩
    obtain ⟨a, ha, hxa⟩ := transitive_sets_cover base x
    obtain ⟨b, hb, hyb⟩ := transitive_sets_cover base y
    obtain ⟨c, hc, hac, hbc⟩ := transitive_sets_directed base ha hb
    obtain ⟨R, hRG, hRB, hR⟩ := augmented_bisimulation_restrict base hc hr
    exact afa_transitive_internal_strong_extensional base hA hc R hRG hRB x y
      ((hR x y).mpr ⟨hac x hxa, hbc y hyb, hxy⟩)
  · rintro rfl
    exact internalBehavior_refl base.empty x

#print axioms afa_internal_behavior_iff_equal
end FullBridge
