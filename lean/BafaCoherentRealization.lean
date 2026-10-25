import DecorationActionLaws
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

/-- One fixed-parameter BAFA realization simultaneously realizes an entire
    supplied family of graph automorphisms and retains its composition table.
    The index type and selection of codes are external, not an internal family. -/
theorem bafa_fixed_coherent_realization (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (one : I) (mul : I → I → I) (act : I → U)
    {t a e : U} (ht : TransitiveCode s t) (hG : GraphCode s a e)
    (hEnd : EndExtensionCode s a e t)
    (hAct : ∀ i, GraphIsoCode s a e a e (act i))
    (hOne : ∀ x y, CodedRelation s (act one) x y → x = y)
    (hMul : ∀ i j x z, CodedRelation s (act (mul i j)) x z ↔
      ∃ y, CodedRelation s (act j) x y ∧ CodedRelation s (act i) y z) :
    ∃ m g T, ∃ out : I → U, LeastGraphRelationCode s a e m ∧
      DecorationCode s a e g ∧ TransitiveCode s T ∧ RangeCode s a g T ∧
      Subset s t T ∧ (∀ x, s x t → CodedRelation s g x x) ∧
      (∀ x y X Y, CodedRelation s g x X → CodedRelation s g y Y →
        (X = Y ↔ CodedRelation s m x y)) ∧
      (∀ i, MembershipIsoCode s T T (out i) ∧ DecorationImageCode s g (act i) (out i)) ∧
      (∀ X Y, CodedRelation s (out one) X Y → X = Y) ∧
      (∀ i j X Z, CodedRelation s (out (mul i j)) X Z ↔
        ∃ Y, CodedRelation s (out j) X Y ∧ CodedRelation s (out i) Y Z) ∧
      (∀ i x y, s x t → s y t → CodedRelation s (act i) x y → CodedRelation s (out i) x y) ∧
      (∀ i X Y, CodedRelation s (out i) X Y → internalCode base X = internalCode base Y) ∧
      (∀ i j, out i = out j ↔ ∀ x y z,
        CodedRelation s (act i) x y → CodedRelation s (act j) x z → CodedRelation s m y z) := by
  classical
  obtain ⟨m, g, hm, hg, hfix, hker⟩ := bafa_fixed_least_decoration base hB ht hG hEnd
  obtain ⟨T, hT, hgT⟩ := decoration_transitive_range base hg
  have hExists : ∀ i, ∃ P, MembershipIsoCode s T T P ∧ DecorationImageCode s g (act i) P :=
    fun i => least_decoration_automorphism_descends base hG hm hg hgT hker (hAct i)
  let out : I → U := fun i => Classical.choose (hExists i)
  have hout : ∀ i, MembershipIsoCode s T T (out i) ∧ DecorationImageCode s g (act i) (out i) :=
    fun i => Classical.choose_spec (hExists i)
  refine ⟨m, g, T, out, hm, hg, hT, hgT, ?_, hfix, hker, hout,
    decoration_image_identity hg.1 (hout one).2 hOne, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hgT x).mpr ⟨x, hEnd.1 x hx, hfix x hx⟩
  · intro i j
    exact decoration_image_composition hg.1 (hAct j) (hAct i).1 (hAct i).2.2.1
      (hout i).1.1 (hout j).2 (hout i).2 (hout (mul i j)).2 (hMul i j)
  · intro i x y hx hy hxy
    exact ((hout i).2 x y).mpr ⟨x, y, hfix x hx, hxy, hfix y hy⟩
  · intro i X Y hXY
    exact ((membership_iso_over_quotient base hT hT (hout i).1).2 X Y hXY).2
  · intro i j
    exact decoration_images_equal_iff base hg.1 (hAct i) (hAct j)
      (hout i).1.1 (hout j).1.1 (hout i).2 (hout j).2 hker

/-- A faithful action on the retained old part remains faithful after any
    common realization fixing that part; no global injectivity is required. -/
theorem fixed_decoration_action_faithful {I : Type v} {t g : U} (act out : I → U)
    (hfix : ∀ x, s x t → CodedRelation s g x x)
    (hout : ∀ i, DecorationImageCode s g (act i) (out i))
    (hfun : ∀ i, ∃ T, FunctionCode s T (out i))
    (hfaithful : ∀ i j, (∀ x y z, s x t → s y t → s z t →
      CodedRelation s (act i) x y → CodedRelation s (act j) x z → y = z) → i = j) :
    ∀ i j, out i = out j → i = j := by
  intro i j hij
  apply hfaithful i j
  intro x y z hx hy hz hxy hxz
  have hXY := (hout i x y).mpr ⟨x, y, hfix x hx, hxy, hfix y hy⟩
  have hXZ := (hout j x z).mpr ⟨x, z, hfix x hx, hxz, hfix z hz⟩
  obtain ⟨T, hf⟩ := hfun j
  exact coded_function_value_unique hf (hij ▸ hXY) hXZ

#print axioms bafa_fixed_coherent_realization
#print axioms fixed_decoration_action_faithful
end FullBridge
