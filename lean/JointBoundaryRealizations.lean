import JointBoundaryFamilies
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

structure JointBoundaryRealization (base : BaseCollection s) {w D N E b : U}
    (P : CodedMaskAction base w) (Q : CodedMaskGraphAction base P N E)
    (K : BoundaryRenaming s D N b P.domain)
    (F : BoundaryGraphAttachment s D N E b P.domain K) where
  action : CodedMaskAction base w
  extendsOld : CodedMaskExtends base P action
  masksEqual : action.masks = P.masks
  kernel : U
  decoration : U
  least : LeastGraphRelationCode s F.domain F.edge kernel
  solution : DecorationCode s F.domain F.edge decoration
  fixed : ∀ x, s x P.domain → CodedRelation s decoration x x
  exactKernel : ∀ x y X Y, CodedRelation s decoration x X → CodedRelation s decoration y Y →
    (X = Y ↔ CodedRelation s kernel x y)
  function : U
  rawSolution : DecorationCode s N E function
  composite : ∀ x X, CodedRelation s function x X ↔
    ∃ v, CodedRelation s K.code x v ∧ CodedRelation s decoration v X
  boundary : ∀ x X, CodedRelation s b x X → CodedRelation s function x X
  values : ∀ x X, CodedRelation s function x X → s X action.domain
  equivariant : ∀ i x y X Y, CodedRelation s (Q.maps i) x y → CodedRelation s function x X →
    CodedRelation s function y Y → CodedRelation s (action.maps i) X Y

theorem bafa_joint_boundary_realization (base : BaseCollection s) (hBAFA : BAFACode s)
    {w D N E b : U} (P : CodedMaskAction base w) (Q : CodedMaskGraphAction base P N E)
    {K : BoundaryRenaming s D N b P.domain} (F : BoundaryGraphAttachment s D N E b P.domain K)
    (hG : GraphCode s N E) (hOld : ∀ x X, CodedRelation s b x X → s X P.domain)
    (hcomp : ∀ i, BoundaryActionCompatible s b (P.maps i) (Q.maps i)) :
    Nonempty (JointBoundaryRealization base P Q K F) := by
  obtain ⟨rho, hrho, hr, hrOne, hrMul⟩ := boundary_group_action base (internalMaskGroup base w)
    F P.transitive P.maps Q.maps P.iso Q.iso hOld hcomp P.one Q.one P.mul Q.mul
  obtain ⟨L, hL, hLcodes⟩ := joint_boundary_action_family base P Q F rho (fun i => (hrho i).1) hr
  obtain ⟨m, g, T, out, hm, hg, hT, hgT, hAT, hfix, hker, hout, hOne, hMul, hOldOut, _⟩ :=
    bafa_fixed_coherent_realization base hBAFA (internalMaskOne base w) (internalMaskMul base)
      rho P.transitive F.graph F.old hrho hrOne hrMul
  obtain ⟨M, hM, hMcodes⟩ := joint_decoration_image_family base P.maskMembers hL rho out hLcodes hout
  let C : CodedMaskAction base w := ⟨T, hT, P.masks, P.maskMembers, M, hM,
    out, hMcodes, fun i => (hout i).1, hOne, hMul⟩
  have hExt : CodedMaskExtends base P C := by
    refine ⟨hAT, ?_⟩
    intro i x y hxy
    exact hOldOut i x y (coded_function_domain (P.iso i).1 hxy)
      (((P.iso i).2.2.1 y).mpr ⟨x, coded_function_domain (P.iso i).1 hxy, hxy⟩)
      ((hr i x y).mpr (Or.inl hxy))
  obtain ⟨f, hf, hfr, hb⟩ := boundary_attachment_decoration_pullback base F hG hg hfix hOld
  refine ⟨⟨C, hExt, rfl, m, g, hm, hg, hfix, hker, f, hf, hfr, hb, ?_, ?_⟩⟩
  · intro x X hxX
    obtain ⟨v, _, hvX⟩ := (hfr x X).mp hxX
    exact (hgT X).mpr ⟨v, coded_function_domain hg.1 hvX, hvX⟩
  · intro i x y X Y hxy hxX hyY
    obtain ⟨u, hxu, huX⟩ := (hfr x X).mp hxX
    obtain ⟨v, hyv, hvY⟩ := (hfr y Y).mp hyY
    exact ((hout i).2 X Y).mpr
      ⟨u, v, huX, (hr i u v).mpr (Or.inr ⟨x, y, hxu, hxy, hyv⟩), hvY⟩

#print axioms bafa_joint_boundary_realization
end FullBridge
