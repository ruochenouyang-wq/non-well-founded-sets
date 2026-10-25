import InjectiveBoundaryCopies
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Extend a prescribed equivariant embedding over a larger source action.
    The target action is retained literally, while the new source is embedded. -/
theorem bafa_coded_mask_embedding_extension (base : BaseCollection s) (hB : BAFACode s)
    {w f : U} (A P Q : CodedMaskAction base w) (E : CodedMaskEmbedding base A P f)
    (hAQ : CodedMaskExtends base A Q) :
    ∃ C : CodedMaskAction base w, ∃ g, CodedMaskExtends base P C ∧
      Nonempty (CodedMaskEmbedding base Q C g) ∧
      ∀ x X, CodedRelation s f x X → CodedRelation s g x X := by
  obtain ⟨e, _, heG, _, he, _⟩ := membership_graph_identity_decoration base Q.transitive
  have hmask : Q.masks = P.masks := base.extensional _ _
    (fun i => (Q.maskMembers i).trans (P.maskMembers i).symm)
  let G : CodedMaskGraphAction base P Q.domain e :=
    ⟨Q.family, hmask ▸ Q.familyFunction, Q.maps, Q.mapCodes,
      fun i => (graph_iso_membership_iff he he).mpr (Q.iso i), Q.one, Q.mul⟩
  have hExt : GraphExtensionalCode s Q.domain e := by
    intro x hx y hy hr
    apply base.extensional
    intro z
    exact ⟨fun hz => ((he y z).mp ((hr z (Q.transitive x hx z hz)).mp ((he x z).mpr ⟨hx, hz⟩))).2,
      fun hz => ((he x z).mp ((hr z (Q.transitive y hy z hz)).mpr ((he y z).mpr ⟨hy, hz⟩))).2⟩
  have hClosed : GraphClosedCode s Q.domain e A.domain :=
    ⟨hAQ.1, fun x hx y hxy => A.transitive x hx y ((he x y).mp hxy).2⟩
  have hf : DecorationCode s A.domain e f := by
    refine ⟨E.iso.1, ?_⟩
    intro x hx X hxX Y
    constructor
    · intro hYX
      have hXr := (E.iso.2.2.1 X).mpr ⟨x, hx, hxX⟩
      obtain ⟨y, hy, hyY⟩ := (E.iso.2.2.1 Y).mp (E.transitive X hXr Y hYX)
      exact ⟨y, hy, (he x y).mpr ⟨hAQ.1 x hx, (E.iso.2.2.2 x y X Y hxX hyY).mpr hYX⟩, hyY⟩
    · rintro ⟨y, _, hxy, hyY⟩
      exact (E.iso.2.2.2 x y X Y hxX hyY).mp ((he x y).mp hxy).2
  have hOld : ∀ x X, CodedRelation s f x X → s X P.domain :=
    fun x X hx => coded_mask_embedding_value base E hx
  have hcomp : ∀ i, BoundaryActionCompatible s f (P.maps i) (G.maps i) := by
    intro i x y X Y hxy hxX hXY
    have hx := coded_function_domain E.iso.1 hxX
    obtain ⟨z, hxz, _⟩ := (A.iso i).1.2 x hx
    have hz := ((A.iso i).2.2.1 z).mpr ⟨x, hx, hxz⟩
    obtain ⟨Z, hzZ, _⟩ := E.iso.1.2 z hz
    have hzy := coded_function_value_unique (Q.iso i).1 (hAQ.2 i x z hxz) hxy
    have hZY := coded_function_value_unique (P.iso i).1 (E.intertwines i x z X Z hxz hxX hzZ) hXY
    exact hzy ▸ hZY ▸ hzZ
  obtain ⟨K⟩ := boundary_renaming_exists base hf.1 hClosed.1 hOld
  obtain ⟨F⟩ := boundary_graph_attachment_exists base K P.transitive hClosed hf hOld
  obtain ⟨R⟩ := bafa_joint_boundary_realization base hB P G F heG hOld hcomp
  have hi := joint_injective_boundary_solution base P G R E.iso.2.1 hExt
  obtain ⟨T, eT, hT, _, heT, hiso⟩ := injective_decoration_graph_iso base R.rawSolution hi
  have hmem := (graph_iso_membership_iff he heT).mp hiso
  have hTC : Subset s T R.action.domain := by
    intro X hX
    obtain ⟨x, _, hxX⟩ := (hmem.2.2.1 X).mp hX
    exact R.values x X hxX
  exact ⟨R.action, R.function, R.extendsOld,
    ⟨⟨T, hT, hTC, hmem, R.equivariant⟩⟩, R.boundary⟩

#print axioms bafa_coded_mask_embedding_extension
end FullBridge
