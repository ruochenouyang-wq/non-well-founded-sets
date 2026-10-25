import InducedGroupAmalgam
namespace FullBridge
universe u v w
variable {U : Type u} {s : U → U → Prop}

/-- Enlarge the acting finite group while preserving every old action value.
    Cosets, the induced graph action and its BAFA realization are constructed. -/
theorem bafa_subgroup_action_extension (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} {J : Type w} {G : FiniteGroupData I} {H : FiniteGroupData J}
    (f : FiniteGroupEmbedding G H) (P : TransitiveGroupAction s G) :
    ∃ Q : TransitiveGroupAction s H, Subset s P.domain Q.domain ∧
      ∀ g x y, CodedRelation s (P.code g) x y → CodedRelation s (Q.code (f.map g)) x y := by
  obtain ⟨S, e, rho, hG, hEnd, hr, hOne, hMul, hExt⟩ := induced_group_graph base f P
  obtain ⟨_, _, C, out, _, _, hC, _, hPC, _, _, hout, hOutOne, hOutMul, hOld, _, _⟩ :=
    bafa_fixed_coherent_realization base hB H.one H.mul rho P.transitive hG hEnd hr hOne hMul
  refine ⟨⟨C, out, hC, fun h => (hout h).1, hOutOne, hOutMul⟩, hPC, ?_⟩
  intro g x y hxy
  have hx := coded_function_domain (P.iso g).1 hxy
  exact hOld (f.map g) x y hx (((P.iso g).2.2.1 y).mpr ⟨x, hx, hxy⟩) (hExt g x y hxy)

theorem bafa_subgroup_cover_extension (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} {J : Type w} {G : FiniteGroupData I} {H : FiniteGroupData J}
    (f : FiniteGroupEmbedding G H) (P : TransitiveGroupAction s G) (x : U) :
    ∃ Q : TransitiveGroupAction s H, Subset s P.domain Q.domain ∧ s x Q.domain ∧
      ∀ g y z, CodedRelation s (P.code g) y z → CodedRelation s (Q.code (f.map g)) y z := by
  obtain ⟨Q, hPQ, hExt⟩ := bafa_subgroup_action_extension base hB f P
  obtain ⟨R, hQR, hxR⟩ := internal_group_action_step base hB H Q x
  exact ⟨R, fun y hy => hQR.1 y (hPQ y hy), hxR,
    fun g y z hyz => hQR.2 (f.map g) y z (hExt g y z hyz)⟩

#print axioms bafa_subgroup_cover_extension
end FullBridge
