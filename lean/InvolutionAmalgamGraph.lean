import InvolutionCopies
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Build an actual two-copy graph over A with an involutive graph automorphism.
    The graph need not be extensional; no BAFA realization is assumed here. -/
theorem involutive_graph_amalgam (base : BaseCollection s) {t p A : U}
    (ht : TransitiveCode s t) (hA : TransitiveCode s A) (htA : Subset s t A)
    (hp : MembershipIsoCode s t t p)
    (hinv : ∀ x y, CodedRelation s p x y → CodedRelation s p y x) :
    ∃ S e r, GraphCode s S e ∧ EndExtensionCode s S e A ∧
      GraphIsoCode s S e S e r ∧
      (∀ x y, CodedRelation s r x y → CodedRelation s r y x) ∧
      (∀ x y, CodedRelation s p x y → CodedRelation s r x y) := by
  obtain ⟨B, k, S, r, hk, hki, hkr, hInt, hpk, hS, hr, hri, hrr, hsym, hrk, hpr⟩ :=
    internal_involution_two_copies base hp hinv htA
  obtain ⟨eA, _, hGA, _, heA, _⟩ := membership_graph_identity_decoration base hA
  obtain ⟨eB, hGB, heB⟩ := transported_membership_graph base hk hkr
  have hEdge := fun {x y X Y} (hx : CodedRelation s k x X) (hy : CodedRelation s k y Y) =>
    transported_membership_edge_iff hki heB hx hy
  have hOld : ∀ X, s X t → ∀ Y, CodedRelation s eB X Y ↔ s Y X := by
    intro X hX Y
    obtain ⟨x, hx, hxX⟩ := (hp.2.2.1 X).mp hX
    constructor
    · intro hXY
      obtain ⟨u, v, huX, hvY, hvu⟩ := (heB X Y).mp hXY
      have hux := hki u x X huX (hpk x X hxX)
      have hvx : s v x := hux ▸ hvu
      have hvt := ht x hx v hvx
      obtain ⟨V, hvV, _⟩ := hp.1.2 v hvt
      have hVY := coded_function_value_unique hk (hpk v V hvV) hvY
      exact hVY ▸ (hp.2.2.2 x v X V hxX hvV).mp hvx
    · intro hYX
      obtain ⟨y, _, hyY⟩ := (hp.2.2.1 Y).mp (ht X hX Y hYX)
      exact (hEdge (hpk x X hxX) (hpk y Y hyY)).mpr
        ((hp.2.2.2 x y X Y hxX hyY).mpr hYX)
  obtain ⟨e, hemem, he⟩ := coded_relation_union base eA eB
  have hGe : GraphCode s S e := by
    intro z hz
    rcases (hemem z).mp hz with hz | hz
    · obtain ⟨x, y, hx, hy, hxy⟩ := hGA z hz
      exact ⟨x, y, (hS x).mpr (Or.inl hx), (hS y).mpr (Or.inl hy), hxy⟩
    · obtain ⟨x, y, hx, hy, hxy⟩ := hGB z hz
      exact ⟨x, y, (hS x).mpr (Or.inr hx), (hS y).mpr (Or.inr hy), hxy⟩
  have hRowA : ∀ x, s x A → ∀ y, CodedRelation s e x y ↔ s y x := by
    intro x hx y
    constructor
    · intro hxy
      rcases (he x y).mp hxy with h | h
      · exact ((heA x y).mp h).2
      · have hxB := (graphCode_endpoints hGB h).1
        exact (hOld x ((hInt x).mp ⟨hxB, hx⟩) y).mp h
    · intro hyx
      exact (he x y).mpr (Or.inl ((heA x y).mpr ⟨hx, hyx⟩))
  have hRowB : ∀ x, s x B → ∀ y, CodedRelation s e x y ↔ CodedRelation s eB x y := by
    intro x hx y
    constructor
    · intro hxy
      rcases (he x y).mp hxy with h | h
      · obtain ⟨hxA, hyx⟩ := (heA x y).mp h
        exact (hOld x ((hInt x).mp ⟨hx, hxA⟩) y).mpr hyx
      · exact h
    · exact fun h => (he x y).mpr (Or.inr h)
  have hCross : ∀ x X, CodedRelation s k x X → ∀ y Y, CodedRelation s r y Y →
      (CodedRelation s e x y ↔ CodedRelation s e X Y) := by
    intro x X hxX y Y hyY
    have hxA := coded_function_domain hk hxX
    have hXB := (hkr X).mpr ⟨x, hxA, hxX⟩
    rw [hRowA x hxA y, hRowB X hXB Y]
    constructor
    · intro hyx
      obtain ⟨Z, hyZ, _⟩ := hk.2 y (hA x hxA y hyx)
      have hZY := coded_function_value_unique hr ((hrk y Z).mpr (Or.inl hyZ)) hyY
      exact (heB X Y).mpr ⟨x, y, hxX, hZY ▸ hyZ, hyx⟩
    · intro hXY
      obtain ⟨u, v, huX, hvY, hvu⟩ := (heB X Y).mp hXY
      have hux := hki u x X huX hxX
      have hvy := hri v y Y ((hrk v Y).mpr (Or.inl hvY)) hyY
      exact hux ▸ hvy ▸ hvu
  refine ⟨S, e, r, hGe, ⟨fun x hx => (hS x).mpr (Or.inl hx), hRowA⟩,
    ⟨hr, hri, hrr, ?_⟩, hsym, hpr⟩
  intro x y X Y hxX hyY
  rcases (hrk x X).mp hxX with h | h
  · exact hCross x X h y Y hyY
  · exact (hCross X x h Y y (hsym y Y hyY)).symm

#print axioms involutive_graph_amalgam
end FullBridge
