import ActionFamilyComponents
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem joint_family_component_embedding (base : BaseCollection s) {w O N E p : U}
    (P Q : CodedMaskAction base w) (hp : s p O) (hQ : ActionFamilyMember base p Q)
    (hPQ : CodedMaskExtends base P Q)
    (hN : ∀ X, s X N ↔ OrbitDiagramNode s O X)
    (hE : ∀ X Y, CodedRelation s E X Y ↔ FamilyDiagramEdge s O X Y)
    (G : CodedMaskGraphAction base P N E)
    (hG : ∀ i X Y, CodedRelation s (G.maps i) X Y ↔ FamilyDiagramMove s O i.val X Y)
    (B : ActionFamilyBoundary s O P.domain N E)
    {K : BoundaryRenaming s B.domain N B.code P.domain}
    {F : BoundaryGraphAttachment s B.domain N E B.code P.domain K}
    (R : JointBoundaryRealization base P G K F) :
    ∃ f, Nonempty (CodedMaskEmbedding base Q R.action f) ∧
      (∀ x, s x P.domain → CodedRelation s f x x) ∧
      ∀ x X, CodedRelation s f x X ↔ s x Q.domain ∧
        ∃ u, IsOrderedPair s u p x ∧ CodedRelation s R.function u X := by
  obtain ⟨e, C, he, hc⟩ := action_family_attached_component base P Q hp hQ hN hE B K F
  obtain ⟨f, hf, hfr⟩ := closed_graph_copy_decoration_pullback base C R.solution
  have hfi := closed_graph_copy_least_pullback_injective base C R.least R.exactKernel hfr
  have htag : ∀ x X, CodedRelation s f x X ↔ s x Q.domain ∧
      ∃ u, IsOrderedPair s u p x ∧ CodedRelation s R.function u X := by
    intro x X
    constructor
    · intro h
      obtain ⟨v, hxv, hvX⟩ := (hfr x X).mp h
      obtain ⟨hx, u, hxu, huv⟩ := (hc x v).mp hxv
      exact ⟨hx, u, hxu, (R.composite u X).mpr ⟨v, huv, hvX⟩⟩
    · rintro ⟨hx, u, hxu, huX⟩
      obtain ⟨v, huv, hvX⟩ := (R.composite u X).mp huX
      exact (hfr x X).mpr ⟨v, (hc x v).mpr ⟨hx, u, hxu, huv⟩, hvX⟩
  obtain ⟨T, eT, hT, _, heT, hiso⟩ := injective_decoration_graph_iso base hf hfi
  have hmem := (graph_iso_membership_iff he heT).mp hiso
  have hTC : Subset s T R.action.domain := by
    intro X hX
    obtain ⟨x, _, hxX⟩ := (hmem.2.2.1 X).mp hX
    obtain ⟨_, u, _, huX⟩ := (htag x X).mp hxX
    exact R.values u X huX
  have hInt : ∀ i x y X Y, CodedRelation s (Q.maps i) x y →
      CodedRelation s f x X → CodedRelation s f y Y → CodedRelation s (R.action.maps i) X Y := by
    intro i x y X Y hxy hxX hyY
    obtain ⟨_, u, hxu, huX⟩ := (htag x X).mp hxX
    obtain ⟨_, v, hyv, hvY⟩ := (htag y Y).mp hyY
    exact R.equivariant i u v X Y
      ((hG i u v).mpr ((family_diagram_move_iff base Q i hp hQ hxu hyv).mpr hxy)) huX hvY
  refine ⟨f, ⟨⟨T, hT, hTC, hmem, hInt⟩⟩, ?_, htag⟩
  intro x hx
  obtain ⟨u, hu⟩ := orderedPair_exists base.pairing p x
  obtain ⟨t, ht⟩ := hQ
  exact (htag x x).mpr ⟨hPQ.1 x hx, u, hu, R.boundary u x
    ((B.values u x).mpr ⟨p, t, Q.domain, Q.family, hp, ht, hx, hu⟩)⟩

/-- A whole internally set-sized family of compatible actions embeds in one
    actual extension, fixing the common action pointwise. The embeddings need
    not have disjoint ranges, but are separately injective and equivariant. -/
theorem bafa_coded_mask_family_amalgamation (base : BaseCollection s) (hB : BAFACode s)
    {w O : U} (P : CodedMaskAction base w) (h : ActionFamilyCode base w O)
    (he : ∀ p Q, s p O → ActionFamilyMember base p Q → CodedMaskExtends base P Q) :
    ∃ C : CodedMaskAction base w, CodedMaskExtends base P C ∧
      ∀ p Q, s p O → ActionFamilyMember base p Q →
        ∃ f, Nonempty (CodedMaskEmbedding base Q C f) ∧
          ∀ x, s x P.domain → CodedRelation s f x x := by
  obtain ⟨N, E, hN, hEG, hE⟩ := action_family_diagram_exists base h
  obtain ⟨G, hG⟩ := action_family_joint_graph_action base P h hN hE
  obtain ⟨B⟩ := action_family_boundary_exists base P h he hN hE
  have hbP := action_family_boundary_old B
  obtain ⟨K⟩ := boundary_renaming_exists base B.decoration.1 B.closed.1 hbP
  obtain ⟨F⟩ := boundary_graph_attachment_exists base K P.transitive B.closed B.decoration hbP
  obtain ⟨R⟩ := bafa_joint_boundary_realization base hB P G F hEG hbP
    (action_family_boundary_compatible base P h he B G hG)
  refine ⟨R.action, R.extendsOld, fun p Q hp hQ => ?_⟩
  obtain ⟨f, hf, hfix, _⟩ := joint_family_component_embedding base P Q hp hQ (he p Q hp hQ)
    hN hE G hG B R
  exact ⟨f, hf, hfix⟩

#print axioms bafa_coded_mask_family_amalgamation
end FullBridge
