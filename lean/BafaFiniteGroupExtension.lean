import FiniteGroupAmalgam
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

/-- Every internally coded action of a specified external finite group on a
    transitive set extends coherently over any larger transitive set, in BAFA.
    The new graph action and its common BAFA realization are both constructed. -/
theorem bafa_finite_group_extension (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (G : FiniteGroupData I) {t A : U}
    (ht : TransitiveCode s t) (hA : TransitiveCode s A) (htA : Subset s t A)
    (act : I → U) (hp : ∀ i, MembershipIsoCode s t t (act i))
    (hOne : ∀ x y, CodedRelation s (act G.one) x y → x = y)
    (hMul : ∀ i j x z, CodedRelation s (act (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (act j) x y ∧ CodedRelation s (act i) y z) :
    ∃ C, ∃ out : I → U, TransitiveCode s C ∧ Subset s A C ∧
      (∀ i, MembershipIsoCode s C C (out i)) ∧
      (∀ X Y, CodedRelation s (out G.one) X Y → X = Y) ∧
      (∀ i j X Z, CodedRelation s (out (G.mul i j)) X Z ↔
        ∃ Y, CodedRelation s (out j) X Y ∧ CodedRelation s (out i) Y Z) ∧
      (∀ i x y, CodedRelation s (act i) x y → CodedRelation s (out i) x y) ∧
      (∀ i X Y, CodedRelation s (out i) X Y → internalCode base X = internalCode base Y) := by
  obtain ⟨S, e, rho, hG, hEnd, hr, hrOne, hrMul, hExt⟩ :=
    finite_group_graph_amalgam base G ht hA htA act hp hOne hMul
  obtain ⟨_, _, C, out, _, _, hC, _, hAC, _, _, hout, hOutOne, hOutMul, hOld, hQ, _⟩ :=
    bafa_fixed_coherent_realization base hB G.one G.mul rho hA hG hEnd hr hrOne hrMul
  refine ⟨C, out, hC, hAC, fun i => (hout i).1, hOutOne, hOutMul, ?_, hQ⟩
  intro i x y hxy
  have hx := coded_function_domain (hp i).1 hxy
  have hy := ((hp i).2.2.1 y).mpr ⟨x, hx, hxy⟩
  exact hOld i x y (htA x hx) (htA y hy) (hExt i x y hxy)

theorem bafa_finite_group_cover_extension (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (G : FiniteGroupData I) {t : U} (ht : TransitiveCode s t)
    (act : I → U) (hp : ∀ i, MembershipIsoCode s t t (act i))
    (hOne : ∀ x y, CodedRelation s (act G.one) x y → x = y)
    (hMul : ∀ i j x z, CodedRelation s (act (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (act j) x y ∧ CodedRelation s (act i) y z) (x : U) :
    ∃ C, ∃ out : I → U, TransitiveCode s C ∧ Subset s t C ∧ s x C ∧
      (∀ i, MembershipIsoCode s C C (out i)) ∧
      (∀ X Y, CodedRelation s (out G.one) X Y → X = Y) ∧
      (∀ i j X Z, CodedRelation s (out (G.mul i j)) X Z ↔
        ∃ Y, CodedRelation s (out j) X Y ∧ CodedRelation s (out i) Y Z) ∧
      (∀ i y z, CodedRelation s (act i) y z → CodedRelation s (out i) y z) := by
  obtain ⟨a, ha, hxa⟩ := transitive_sets_cover base x
  obtain ⟨A, hA, htA, haA⟩ := transitive_sets_directed base ht ha
  obtain ⟨C, out, hC, hAC, hout, hO, hM, hE, _⟩ :=
    bafa_finite_group_extension base hB G ht hA htA act hp hOne hMul
  exact ⟨C, out, hC, fun y hy => hAC y (htA y hy), hAC x (haA x hxa), hout, hO, hM, hE⟩

#print axioms bafa_finite_group_extension
#print axioms bafa_finite_group_cover_extension
end FullBridge
