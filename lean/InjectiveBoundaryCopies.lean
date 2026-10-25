import BoundedCollectionCandidate
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- An injective prescribed boundary prevents all additional collisions in
    its fresh-name extension, including between different boundary points. -/
theorem boundary_renaming_injective {D N b A : U}
    (K : BoundaryRenaming s D N b A) (hb : InjectiveCode s b) : InjectiveCode s K.code := by
  intro x y Z hx hy
  rcases K.collision x y Z hx hy with h | ⟨hx, hy⟩
  · exact h
  · exact hb x y Z hx hy

/-- Gluing an injective boundary preserves the entire supplied extensional
    graph as a closed extensional copy, not only a selected component. -/
theorem injective_boundary_closed_copy {D N E b A : U}
    (K : BoundaryRenaming s D N b A)
    (F : BoundaryGraphAttachment s D N E b A K)
    (hki : InjectiveCode s K.code) (hExt : GraphExtensionalCode s N E) :
    ∃ C : ClosedGraphCopy s F.domain F.edge N E, C.code = K.code := by
  have htransport : ∀ x y X Y, CodedRelation s K.code x X → CodedRelation s K.code y Y →
      (CodedRelation s F.edge X Y ↔ CodedRelation s E x y) := by
    intro x y X Y hx hy
    rw [F.rows x X hx Y]
    exact ⟨fun ⟨z, hxz, hz⟩ => (hki z y Y hz hy) ▸ hxz, fun h => ⟨y, h, hy⟩⟩
  have hext : GraphExtensionalCode s K.domain F.edge := by
    intro X hX Y hY hrows
    obtain ⟨x, hx, hxX⟩ := (K.range X).mp hX
    obtain ⟨y, hy, hyY⟩ := (K.range Y).mp hY
    have hxy : x = y := by
      apply hExt x hx y hy
      intro z hz
      obtain ⟨Z, hzZ, _⟩ := K.function.2 z hz
      exact (htransport x z X Z hxX hzZ).symm.trans
        ((hrows Z ((K.range Z).mpr ⟨z, hz, hzZ⟩)).trans (htransport y z Y Z hyY hzZ))
    exact coded_function_value_unique K.function (hxy ▸ hxX) hyY
  exact ⟨⟨K.domain, K.code, K.function, hki, K.range, F.closed, htransport, hext⟩, rfl⟩

/-- Exact least kernels preserve injectivity of the raw boundary pullback. -/
theorem joint_injective_boundary_solution (base : BaseCollection s) {w D N E b : U}
    (P : CodedMaskAction base w) (G : CodedMaskGraphAction base P N E)
    {K : BoundaryRenaming s D N b P.domain}
    {F : BoundaryGraphAttachment s D N E b P.domain K}
    (R : JointBoundaryRealization base P G K F)
    (hb : InjectiveCode s b) (hExt : GraphExtensionalCode s N E) :
    InjectiveCode s R.function := by
  obtain ⟨C, hc⟩ := injective_boundary_closed_copy K F (boundary_renaming_injective K hb) hExt
  apply closed_graph_copy_least_pullback_injective base C R.least R.exactKernel
  simpa only [hc] using R.composite

#print axioms joint_injective_boundary_solution
end FullBridge
