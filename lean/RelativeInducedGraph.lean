import RelativeInducedFunctions
namespace FullBridge
universe u v w
variable {U : Type u} {s : U → U → Prop}

/-- Induce an old subgroup action to a larger finite group on an actual graph
    end-extending the old transitive domain. -/
theorem relative_induced_group_graph (base : BaseCollection s) {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (P : TransitiveGroupAction s G) (Q : TransitiveGroupAction s H)
    (hPQ : CoreActionCompatible f P Q) :
    ∃ S e, ∃ rho : J → U, GraphCode s S e ∧ EndExtensionCode s S e P.domain ∧
      (∀ h, GraphIsoCode s S e S e (rho h)) ∧
      (∀ X Y, CodedRelation s (rho H.one) X Y → X = Y) ∧
      (∀ h k X Z, CodedRelation s (rho (H.mul h k)) X Z ↔
        ∃ Y, CodedRelation s (rho k) X Y ∧ CodedRelation s (rho h) Y Z) ∧
      (∀ g x y, CodedRelation s (P.code g) x y → CodedRelation s (rho (f.map g)) x y) ∧
      (∀ h x y, CodedRelation s (Q.code h) x y → CodedRelation s (rho h) x y) := by
  classical
  have hBase : ∀ x y, CodedRelation s (Q.code (cosetRepresentative f (cosetBase f))) x y → x = y := by
    intro x y hxy
    rw [coset_representative_base] at hxy
    exact Q.identity x y hxy
  obtain ⟨ranges, codes, S, e, hIdRange, hId, hc, hInt, hS, hGraph, hEnd, hClosed, hEdges⟩ :=
    finite_membership_amalgam base Q.transitive P.transitive hPQ.1 (cosetBase f)
      (fun c => Q.code (cosetRepresentative f c)) (fun c => Q.iso (cosetRepresentative f c))
      hBase (cosetIndices f) (coset_indices_complete f)
  obtain ⟨rho, hr⟩ := relative_induced_action_functions base f P Q hPQ ranges codes hc hInt hS
  have hR := fun h => (hr h).2.1
  have hTarget : ∀ h X Y, CodedRelation s (rho h) X Y → s Y S := by
    intro h X Y hXY
    obtain ⟨c, x, y, _, _, hyY⟩ := (hR h X Y).mp hXY
    exact (hS Y).mpr ⟨cosetAction f h c, ((hc (cosetAction f h c)).2.2.1 Y).mpr
      ⟨y, coded_function_domain (hc (cosetAction f h c)).1 hyY, hyY⟩⟩
  have hOne : ∀ X Y, CodedRelation s (rho H.one) X Y → X = Y := by
    intro X Y hXY
    obtain ⟨c, x, y, hxX, hxy, hyY⟩ := (hR H.one X Y).mp hXY
    rw [coset_factor_identity] at hxy
    rw [coset_action_identity] at hyY
    have hxy' := P.identity x y hxy
    exact coded_function_value_unique (hc c).1 hxX (hxy'.symm ▸ hyY)
  have hMulForward : ∀ h k X Z, CodedRelation s (rho (H.mul h k)) X Z →
      ∃ Y, CodedRelation s (rho k) X Y ∧ CodedRelation s (rho h) Y Z := by
    intro h k X Z hXZ
    obtain ⟨c, x, z, hxX, hxz, hzZ⟩ := (hR (H.mul h k) X Z).mp hXZ
    rw [coset_factor_multiplication] at hxz
    obtain ⟨y, hxy, hyz⟩ := (P.multiplication _ _ x z).mp hxz
    have hy := ((P.iso (cosetFactor f k c)).2.2.1 y).mpr
      ⟨x, coded_function_domain (P.iso (cosetFactor f k c)).1 hxy, hxy⟩
    obtain ⟨Y, hyY, _⟩ := (hc (cosetAction f k c)).1.2 y hy
    exact ⟨Y, (hR k X Y).mpr ⟨c, x, y, hxX, hxy, hyY⟩,
      (hR h Y Z).mpr ⟨cosetAction f k c, y, z, hyY, hyz,
        by simpa only [coset_action_multiplication] using hzZ⟩⟩
  have hMul : ∀ h k X Z, CodedRelation s (rho (H.mul h k)) X Z ↔
      ∃ Y, CodedRelation s (rho k) X Y ∧ CodedRelation s (rho h) Y Z := by
    intro h k X Z
    refine ⟨hMulForward h k X Z, ?_⟩
    rintro ⟨Y, hXY, hYZ⟩
    obtain ⟨Z', hXZ', _⟩ := (hr (H.mul h k)).1.2 X (coded_function_domain (hr k).1 hXY)
    obtain ⟨Y', hXY', hY'Z'⟩ := hMulForward h k X Z' hXZ'
    have hY'Y := coded_function_value_unique (hr k).1 hXY' hXY
    have hZ'Z := coded_function_value_unique (hr h).1 (hY'Y ▸ hY'Z') hYZ
    exact hZ'Z ▸ hXZ'
  have hInv : ∀ h X Y, CodedRelation s (rho h) X Y ↔ CodedRelation s (rho (H.inv h)) Y X := by
    intro h X Y
    constructor
    · intro hXY
      obtain ⟨Z, hYZ, _⟩ := (hr (H.inv h)).1.2 Y (hTarget h X Y hXY)
      have hXZ := (hMul (H.inv h) h X Z).mpr ⟨Y, hXY, hYZ⟩
      rw [H.inv_mul] at hXZ
      exact (hOne X Z hXZ).symm ▸ hYZ
    · intro hYX
      obtain ⟨Z, hXZ, _⟩ := (hr h).1.2 X (hTarget (H.inv h) Y X hYX)
      have hYZ := (hMul h (H.inv h) Y Z).mpr ⟨X, hYX, hXZ⟩
      rw [H.mul_inv] at hYZ
      exact (hOne Y Z hYZ).symm ▸ hXZ
  have hForward : ∀ h X Y X' Y', CodedRelation s (rho h) X X' →
      CodedRelation s (rho h) Y Y' → CodedRelation s e X Y → CodedRelation s e X' Y' := by
    intro h X Y X' Y' hXX' hYY' hXY
    obtain ⟨c, x, x', hxX, hxx', hx'X'⟩ := (hR h X X').mp hXX'
    have hXc := ((hc c).2.2.1 X).mpr ⟨x, coded_function_domain (hc c).1 hxX, hxX⟩
    obtain ⟨y, hy, hyY⟩ := ((hc c).2.2.1 Y).mp ((hClosed c).2 X hXc Y hXY)
    obtain ⟨y', hyy', _⟩ := (P.iso (cosetFactor f h c)).1.2 y hy
    have hy' := ((P.iso (cosetFactor f h c)).2.2.1 y').mpr ⟨y, hy, hyy'⟩
    obtain ⟨Z, hy'Z, _⟩ := (hc (cosetAction f h c)).1.2 y' hy'
    have hYZ := (hR h Y Z).mpr ⟨c, y, y', hyY, hyy', hy'Z⟩
    have hZY' := coded_function_value_unique (hr h).1 hYZ hYY'
    have hyx := (hEdges c x y X Y hxX hyY).mp hXY
    have hy'x' := (P.iso (cosetFactor f h c)).2.2.2 x y x' y' hxx' hyy' |>.mp hyx
    exact hZY' ▸ (hEdges (cosetAction f h c) x' y' X' Z hx'X' hy'Z).mpr hy'x'
  have hIso : ∀ h, GraphIsoCode s S e S e (rho h) := by
    intro h
    refine ⟨(hr h).1, ?_, ?_, ?_⟩
    · intro X Y Z hXZ hYZ
      exact coded_function_value_unique (hr (H.inv h)).1 ((hInv h X Z).mp hXZ) ((hInv h Y Z).mp hYZ)
    · intro Y
      constructor
      · intro hY
        obtain ⟨X, hYX, _⟩ := (hr (H.inv h)).1.2 Y hY
        exact ⟨X, hTarget (H.inv h) Y X hYX, (hInv h X Y).mpr hYX⟩
      · exact fun ⟨X, _, hXY⟩ => hTarget h X Y hXY
    · intro X Y X' Y' hXX' hYY'
      exact ⟨hForward h X Y X' Y' hXX' hYY',
        hForward (H.inv h) X' Y' X Y ((hInv h X X').mp hXX') ((hInv h Y Y').mp hYY')⟩
  refine ⟨S, e, rho, hGraph, hEnd, hIso, hOne, hMul, ?_, ?_⟩
  ·
    intro g x y hxy
    have hx := coded_function_domain (P.iso g).1 hxy
    have hy := ((P.iso g).2.2.1 y).mpr ⟨x, hx, hxy⟩
    exact (hR (f.map g) x y).mpr ⟨cosetBase f, x, y, (hId x x).mpr ⟨hx, rfl⟩,
      by simpa only [coset_factor_subgroup_base] using hxy,
      by simpa only [coset_action_subgroup_base] using (hId y y).mpr ⟨hy, rfl⟩⟩
  · intro h x y hxy
    have hx := coded_function_domain (Q.iso h).1 hxy
    have hxS := (hS x).mpr ⟨cosetBase f, (hc (cosetBase f)).2.2.2.1 x hx⟩
    obtain ⟨Y, hxY, _⟩ := (hr h).1.2 x hxS
    have he := coded_function_value_unique (Q.iso h).1 ((hr h).2.2 x Y hx hxY) hxy
    exact he ▸ hxY

#print axioms relative_induced_group_graph
end FullBridge
