import JointAttachmentFamilies
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The whole-mask graph attachment retains an actual joint source code
    after the common BAFA realization, so it can be used as a chain stage. -/
theorem bafa_joint_graph_attachment (base : BaseCollection s) (hBafa : BAFACode s)
    {w t a r : U} (P : CodedMaskAction base w) (Q : CodedMaskGraphAction base P a r)
    (ht : TransitiveCode s t) (htA : Subset s t P.domain)
    (hG : GraphCode s a r) (hExt : GraphExtensionalCode s a r) (hEnd : EndExtensionCode s a r t)
    (hstable : ∀ i x y, s x t → CodedRelation s (P.maps i) x y → s y t)
    (hag : ∀ i x y, s x t → (CodedRelation s (P.maps i) x y ↔ CodedRelation s (Q.maps i) x y)) :
    ∃ C : CodedMaskAction base w, ∃ f,
      Subset s P.domain C.domain ∧ C.masks = P.masks ∧
      DecorationCode s a r f ∧ InjectiveCode s f ∧
      (∀ x, s x t → CodedRelation s f x x) ∧
      (∀ x X, CodedRelation s f x X → s X C.domain) ∧
      (∀ i x y, CodedRelation s (P.maps i) x y → CodedRelation s (C.maps i) x y) ∧
      (∀ i x y X Y, CodedRelation s (Q.maps i) x y → CodedRelation s f x X →
        CodedRelation s f y Y → CodedRelation s (C.maps i) X Y) := by
  obtain ⟨D⟩ := member_graph_attachment_exists base ht P.transitive htA hG hEnd
  obtain ⟨rho, hrho, hr, hrOne, hrMul⟩ := attachment_group_action base (internalMaskGroup base w)
    D P.transitive P.maps Q.maps P.iso Q.iso hstable hag P.one Q.one P.mul Q.mul
  obtain ⟨K, hK, hKcodes⟩ := joint_attachment_action_family base P Q D rho (fun i => (hrho i).1) hr
  obtain ⟨m, g, T, out, hm, hg, hT, hgT, hAT, hfix, hker, hout, hOne, hMul, hOld, _⟩ :=
    bafa_fixed_coherent_realization base hBafa (internalMaskOne base w) (internalMaskMul base)
      rho P.transitive D.graph D.old hrho hrOne hrMul
  obtain ⟨L, hL, hLcodes⟩ := joint_decoration_image_family base P.maskMembers hK rho out hKcodes hout
  let C : CodedMaskAction base w := ⟨T, hT, P.masks, P.maskMembers, L, hL,
    out, hLcodes, fun i => (hout i).1, hOne, hMul⟩
  obtain ⟨f, hf, hfr⟩ := attachment_decoration_pullback base D hG hg
  refine ⟨C, f, hAT, rfl, hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y Z hxZ hyZ
    obtain ⟨X, hxX, hXZ⟩ := (hfr x Z).mp hxZ
    obtain ⟨Y, hyY, hYZ⟩ := (hfr y Z).mp hyZ
    have hXB := (D.copyRange X).mpr ⟨x, coded_function_domain D.copyFunction hxX, hxX⟩
    have hYB := (D.copyRange Y).mpr ⟨y, coded_function_domain D.copyFunction hyY, hyY⟩
    have hXY := least_relation_preserves_closed_extensional base D.closed
      (attachment_closed_extensional D hExt) hm hXB hYB ((hker X Y Z Z hXZ hYZ).mp rfl)
    exact D.copyInjective x y Y (hXY ▸ hxX) hyY
  · intro x hx
    exact (hfr x x).mpr ⟨x, D.fixed x hx, hfix x (htA x hx)⟩
  · intro x X hxX
    obtain ⟨u, _, huX⟩ := (hfr x X).mp hxX
    exact (hgT X).mpr ⟨u, coded_function_domain hg.1 huX, huX⟩
  · intro i x y hxy
    exact hOld i x y (coded_function_domain (P.iso i).1 hxy)
      (((P.iso i).2.2.1 y).mpr ⟨x, coded_function_domain (P.iso i).1 hxy, hxy⟩)
      ((hr i x y).mpr (Or.inl hxy))
  · intro i x y X Y hxy hxX hyY
    obtain ⟨u, hxu, huX⟩ := (hfr x X).mp hxX
    obtain ⟨v, hyv, hvY⟩ := (hfr y Y).mp hyY
    exact ((hout i).2 X Y).mpr ⟨u, v, huX, (hr i u v).mpr (Or.inr ⟨x, y, hxu, hxy, hyv⟩), hvY⟩

#print axioms bafa_joint_graph_attachment
end FullBridge
