import LeastDecorationSymmetry
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Extend an internal involution to an actual transitive set containing A.
    The BAFA decoration fixes A and has the least relation as its exact kernel. -/
theorem bafa_involution_extension (base : BaseCollection s) (hB : BAFACode s)
    {t p A : U} (ht : TransitiveCode s t) (hA : TransitiveCode s A)
    (htA : Subset s t A) (hp : MembershipIsoCode s t t p)
    (hs : ∀ x y, CodedRelation s p x y → CodedRelation s p y x) :
    ∃ C P, TransitiveCode s C ∧ Subset s A C ∧ MembershipIsoCode s C C P ∧
      (∀ x y, CodedRelation s P x y → CodedRelation s P y x) ∧
      (∀ x y, CodedRelation s p x y → CodedRelation s P x y) := by
  obtain ⟨S, e, r, hG, hEnd, hR, hRs, hpr⟩ :=
    involutive_graph_amalgam base ht hA htA hp hs
  obtain ⟨m, g, hm, hg, hfix, hker⟩ :=
    bafa_fixed_least_decoration base hB hA hG hEnd
  obtain ⟨C, hC, hCg⟩ := decoration_transitive_range base hg
  obtain ⟨P, hP, hPs, hPr⟩ :=
    least_decoration_involution_descends base hG hm hg hCg hker hR hRs
  refine ⟨C, P, hC, ?_, hP, hPs, ?_⟩
  · intro x hx
    exact (hCg x).mpr ⟨x, hEnd.1 x hx, hfix x hx⟩
  · intro x y hxy
    have hx := coded_function_domain hp.1 hxy
    have hy := (hp.2.2.1 y).mpr ⟨x, hx, hxy⟩
    exact (hPr x y).mpr ⟨x, y, hfix x (htA x hx), hpr x y hxy,
      hfix y (htA y hy)⟩

/-- Include any prescribed object while retaining the old internal involution. -/
theorem bafa_involution_cover_extension (base : BaseCollection s) (hB : BAFACode s)
    {t p : U} (ht : TransitiveCode s t) (hp : MembershipIsoCode s t t p)
    (hs : ∀ x y, CodedRelation s p x y → CodedRelation s p y x) (x : U) :
    ∃ C P, TransitiveCode s C ∧ Subset s t C ∧ s x C ∧ MembershipIsoCode s C C P ∧
      (∀ y z, CodedRelation s P y z → CodedRelation s P z y) ∧
      (∀ y z, CodedRelation s p y z → CodedRelation s P y z) := by
  obtain ⟨a, ha, hxa⟩ := transitive_sets_cover base x
  obtain ⟨A, hA, htA, haA⟩ := transitive_sets_directed base ht ha
  obtain ⟨C, P, hC, hAC, hP, hPs, hpP⟩ :=
    bafa_involution_extension base hB ht hA htA hp hs
  exact ⟨C, P, hC, fun z hz => hAC z (htA z hz), hAC x (haA x hxa), hP, hPs, hpP⟩

#print axioms bafa_involution_extension
#print axioms bafa_involution_cover_extension
end FullBridge
