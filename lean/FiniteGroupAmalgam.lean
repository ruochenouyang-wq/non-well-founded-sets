import FiniteGroupCopies
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

/-- The new graph action is constructed from the old action: finite copies,
    transitions, inverse maps, edges and all multiplication laws are verified. -/
theorem finite_group_graph_amalgam (base : BaseCollection s) {I : Type v} (G : FiniteGroupData I)
    {t A : U} (ht : TransitiveCode s t) (hA : TransitiveCode s A) (htA : Subset s t A)
    (act : I → U) (hp : ∀ i, MembershipIsoCode s t t (act i))
    (hOne : ∀ x y, CodedRelation s (act G.one) x y → x = y)
    (hMul : ∀ i j x z, CodedRelation s (act (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (act j) x y ∧ CodedRelation s (act i) y z) :
    ∃ S e, ∃ rho : I → U, GraphCode s S e ∧ EndExtensionCode s S e A ∧
      (∀ i, GraphIsoCode s S e S e (rho i)) ∧
      (∀ X Y, CodedRelation s (rho G.one) X Y → X = Y) ∧
      (∀ i j X Z, CodedRelation s (rho (G.mul i j)) X Z ↔
        ∃ Y, CodedRelation s (rho j) X Y ∧ CodedRelation s (rho i) Y Z) ∧
      (∀ i x y, CodedRelation s (act i) x y → CodedRelation s (rho i) x y) := by
  obtain ⟨ranges, codes, S, e, hIdRange, hId, hc, hInt, hS, hG, hEnd, hClosed, hEdges⟩ :=
    finite_membership_amalgam base ht hA htA G.one act hp hOne G.indices G.complete
  obtain ⟨rho, hr⟩ := finite_copy_action_functions base G act ranges codes hp hc hInt hS hMul
  have hR := fun i => (hr i).2
  have hTarget : ∀ i X Y, CodedRelation s (rho i) X Y → s Y S := by
    intro i X Y hXY
    obtain ⟨k, x, _, hxY⟩ := (hR i X Y).mp hXY
    exact (hS Y).mpr ⟨G.mul i k, ((hc (G.mul i k)).2.2.1 Y).mpr
      ⟨x, coded_function_domain (hc (G.mul i k)).1 hxY, hxY⟩⟩
  have hInv : ∀ i X Y, CodedRelation s (rho (G.inv i)) Y X ↔ CodedRelation s (rho i) X Y := by
    intro i X Y
    constructor
    · intro hYX
      obtain ⟨k, x, hxY, hxX⟩ := (hR (G.inv i) Y X).mp hYX
      exact (hR i X Y).mpr ⟨G.mul (G.inv i) k, x, hxX,
        by simpa only [finite_group_right_inverse] using hxY⟩
    · intro hXY
      obtain ⟨k, x, hxX, hxY⟩ := (hR i X Y).mp hXY
      exact (hR (G.inv i) Y X).mpr ⟨G.mul i k, x, hxY,
        by simpa only [finite_group_left_inverse] using hxX⟩
  have hForward : ∀ i X Y X' Y', CodedRelation s (rho i) X X' →
      CodedRelation s (rho i) Y Y' → CodedRelation s e X Y → CodedRelation s e X' Y' := by
    intro i X Y X' Y' hXX' hYY' hXY
    obtain ⟨k, x, hxX, hxX'⟩ := (hR i X X').mp hXX'
    have hX := ((hc k).2.2.1 X).mpr ⟨x, coded_function_domain (hc k).1 hxX, hxX⟩
    have hY := (hClosed k).2 X hX Y hXY
    obtain ⟨y, hy, hyY⟩ := ((hc k).2.2.1 Y).mp hY
    obtain ⟨Z, hyZ, _⟩ := (hc (G.mul i k)).1.2 y hy
    have hYZ := (hR i Y Z).mpr ⟨k, y, hyY, hyZ⟩
    have hZY' := coded_function_value_unique (hr i).1 hYZ hYY'
    exact hZY' ▸ (hEdges (G.mul i k) x y X' Z hxX' hyZ).mpr
      ((hEdges k x y X Y hxX hyY).mp hXY)
  have hIso : ∀ i, GraphIsoCode s S e S e (rho i) := by
    intro i
    refine ⟨(hr i).1, ?_, ?_, ?_⟩
    · intro X Y Z hXZ hYZ
      exact coded_function_value_unique (hr (G.inv i)).1 ((hInv i X Z).mpr hXZ) ((hInv i Y Z).mpr hYZ)
    · intro Y
      constructor
      · intro hY
        obtain ⟨X, hYX, _⟩ := (hr (G.inv i)).1.2 Y hY
        exact ⟨X, hTarget (G.inv i) Y X hYX, (hInv i X Y).mp hYX⟩
      · exact fun ⟨X, _, hXY⟩ => hTarget i X Y hXY
    · intro X Y X' Y' hXX' hYY'
      exact ⟨hForward i X Y X' Y' hXX' hYY',
        hForward (G.inv i) X' Y' X Y ((hInv i X X').mpr hXX') ((hInv i Y Y').mpr hYY')⟩
  refine ⟨S, e, rho, hG, hEnd, hIso, ?_, ?_, ?_⟩
  · intro X Y hXY
    obtain ⟨k, x, hxX, hxY⟩ := (hR G.one X Y).mp hXY
    exact coded_function_value_unique (hc k).1 hxX (by simpa only [G.one_mul] using hxY)
  · intro i j X Z
    constructor
    · intro hXZ
      obtain ⟨k, x, hxX, hxZ⟩ := (hR (G.mul i j) X Z).mp hXZ
      obtain ⟨Y, hxY, _⟩ := (hc (G.mul j k)).1.2 x (coded_function_domain (hc k).1 hxX)
      exact ⟨Y, (hR j X Y).mpr ⟨k, x, hxX, hxY⟩,
        (hR i Y Z).mpr ⟨G.mul j k, x, hxY, by simpa only [G.assoc] using hxZ⟩⟩
    · rintro ⟨Y, hXY, hYZ⟩
      obtain ⟨k, x, hxX, hxY⟩ := (hR j X Y).mp hXY
      obtain ⟨Z', hxZ', _⟩ := (hc (G.mul (G.mul i j) k)).1.2 x (coded_function_domain (hc k).1 hxX)
      have hYZ' := (hR i Y Z').mpr ⟨G.mul j k, x, hxY, by simpa only [G.assoc] using hxZ'⟩
      have hZ'Z := coded_function_value_unique (hr i).1 hYZ' hYZ
      exact (hR (G.mul i j) X Z).mpr ⟨k, x, hxX, hZ'Z ▸ hxZ'⟩
  · intro i x y hxy
    have hx := coded_function_domain (hp i).1 hxy
    exact (hR i x y).mpr ⟨G.one, x, (hId x x).mpr ⟨htA x hx, rfl⟩,
      by simpa only [G.mul_one] using (hc i).2.2.2.2 x y hxy⟩

#print axioms finite_group_graph_amalgam
end FullBridge
