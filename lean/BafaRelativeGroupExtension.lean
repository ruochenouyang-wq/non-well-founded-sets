import RelativeInducedGraph
namespace FullBridge
universe u v w
variable {U : Type u} {s : U → U → Prop}

/-- Enlarge the acting group while fixing the old domain and simultaneously
    preserving a prescribed action of the new group on its transitive core. -/
theorem bafa_relative_subgroup_extension (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} {J : Type w} {G : FiniteGroupData I} {H : FiniteGroupData J}
    (f : FiniteGroupEmbedding G H) (P : TransitiveGroupAction s G) (Q : TransitiveGroupAction s H)
    (hPQ : CoreActionCompatible f P Q) :
    ∃ R : TransitiveGroupAction s H, Subset s P.domain R.domain ∧
      (∀ g x y, CodedRelation s (P.code g) x y → CodedRelation s (R.code (f.map g)) x y) ∧
      GroupActionExtends Q R := by
  obtain ⟨S, e, rho, hG, hEnd, hr, hOne, hMul, hOldP, hOldQ⟩ := relative_induced_group_graph base f P Q hPQ
  obtain ⟨_, _, C, out, _, _, hC, _, hPC, _, _, hout, hOutOne, hOutMul, hOld, _, _⟩ :=
    bafa_fixed_coherent_realization base hB H.one H.mul rho P.transitive hG hEnd hr hOne hMul
  refine ⟨⟨C, out, hC, fun h => (hout h).1, hOutOne, hOutMul⟩, hPC, ?_, ?_⟩
  · intro g x y hxy
    have hx := coded_function_domain (P.iso g).1 hxy
    exact hOld (f.map g) x y hx (((P.iso g).2.2.1 y).mpr ⟨x, hx, hxy⟩) (hOldP g x y hxy)
  · refine ⟨fun x hx => hPC x (hPQ.1 x hx), ?_⟩
    intro h x y hxy
    have hx := coded_function_domain (Q.iso h).1 hxy
    have hy := ((Q.iso h).2.2.1 y).mpr ⟨x, hx, hxy⟩
    exact hOld h x y (hPQ.1 x hx) (hPQ.1 y hy) (hOldQ h x y hxy)

theorem bafa_relative_subgroup_cover_extension (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} {J : Type w} {G : FiniteGroupData I} {H : FiniteGroupData J}
    (f : FiniteGroupEmbedding G H) (P : TransitiveGroupAction s G) (Q : TransitiveGroupAction s H)
    (hPQ : CoreActionCompatible f P Q) (x : U) :
    ∃ R : TransitiveGroupAction s H, Subset s P.domain R.domain ∧ s x R.domain ∧
      (∀ g y z, CodedRelation s (P.code g) y z → CodedRelation s (R.code (f.map g)) y z) ∧
      GroupActionExtends Q R := by
  obtain ⟨R, hPR, hExt, hQR⟩ := bafa_relative_subgroup_extension base hB f P Q hPQ
  obtain ⟨T, hRT, hxT⟩ := internal_group_action_step base hB H R x
  exact ⟨T, fun y hy => hRT.1 y (hPR y hy), hxT,
    fun g y z hyz => hRT.2 (f.map g) y z (hExt g y z hyz),
    ⟨fun y hy => hRT.1 y (hQR.1 y hy), fun h y z hyz => hRT.2 h y z (hQR.2 h y z hyz)⟩⟩

#print axioms bafa_relative_subgroup_cover_extension
end FullBridge
