import JointMaskAmalgams
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

theorem external_group_left_inverse {I : Type v} (G : ExternalGroupData I) (i k : I) :
    G.mul (G.inv i) (G.mul i k) = k := by
  rw [← G.assoc, G.inv_mul, G.one_mul]

theorem external_group_right_inverse {I : Type v} (G : ExternalGroupData I) (i k : I) :
    G.mul i (G.mul (G.inv i) k) = k := by
  rw [← G.assoc, G.mul_inv, G.one_mul]

theorem general_copy_action_compatible {I : Type v} (G : ExternalGroupData I)
    {t A : U} (act ranges codes : I → U)
    (hp : ∀ i, MembershipIsoCode s t t (act i))
    (hc : ∀ i, CopyCode s t A (act i) (ranges i) (codes i))
    (hInt : ∀ i j, i ≠ j → ∀ x, s x (ranges i) ∧ s x (ranges j) ↔ s x t)
    (hMul : ∀ i j x z, CodedRelation s (act (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (act j) x y ∧ CodedRelation s (act i) y z)
    (i k l : I) {x z X Y Z : U}
    (hxX : CodedRelation s (codes k) x X) (hxY : CodedRelation s (codes (G.mul i k)) x Y)
    (hzX : CodedRelation s (codes l) z X) (hzZ : CodedRelation s (codes (G.mul i l)) z Z) : Y = Z := by
  by_cases hkl : k = l
  · subst l
    have hxz := (hc k).2.1 x z X hxX hzX
    exact coded_function_value_unique (hc (G.mul i k)).1 hxY (hxz.symm ▸ hzZ)
  · have hXt := (hInt k l hkl X).mp
      ⟨((hc k).2.2.1 X).mpr ⟨x, coded_function_domain (hc k).1 hxX, hxX⟩,
        ((hc l).2.2.1 X).mpr ⟨z, coded_function_domain (hc l).1 hzX, hzX⟩⟩
    have hpxX := copy_reflects_old_value (hp k) (hc k) hxX hXt
    have hpzX := copy_reflects_old_value (hp l) (hc l) hzX hXt
    obtain ⟨W, hXW, _⟩ := (hp i).1.2 X hXt
    have hxW := (hMul i k x W).mpr ⟨X, hpxX, hXW⟩
    have hzW := (hMul i l z W).mpr ⟨X, hpzX, hXW⟩
    have hYW := coded_function_value_unique (hc (G.mul i k)).1 hxY ((hc (G.mul i k)).2.2.2.2 x W hxW)
    have hZW := coded_function_value_unique (hc (G.mul i l)).1 hzZ ((hc (G.mul i l)).2.2.2.2 z W hzW)
    exact hYW.trans hZW.symm

theorem general_copy_action_total_unique {I : Type v} (G : ExternalGroupData I)
    {t A S : U} (act ranges codes : I → U)
    (hp : ∀ i, MembershipIsoCode s t t (act i))
    (hc : ∀ i, CopyCode s t A (act i) (ranges i) (codes i))
    (hInt : ∀ i j, i ≠ j → ∀ x, s x (ranges i) ∧ s x (ranges j) ↔ s x t)
    (hS : ∀ X, s X S ↔ ∃ i, s X (ranges i))
    (hMul : ∀ i j x z, CodedRelation s (act (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (act j) x y ∧ CodedRelation s (act i) y z) (i : I) :
    ∀ X, s X S → ∃ Y,
      (∃ k x, CodedRelation s (codes k) x X ∧ CodedRelation s (codes (G.mul i k)) x Y) ∧
      ∀ Z, (∃ k x, CodedRelation s (codes k) x X ∧ CodedRelation s (codes (G.mul i k)) x Z) → Z = Y := by
  intro X hX
  obtain ⟨k, hXk⟩ := (hS X).mp hX
  obtain ⟨x, hx, hxX⟩ := ((hc k).2.2.1 X).mp hXk
  obtain ⟨Y, hxY, _⟩ := (hc (G.mul i k)).1.2 x hx
  refine ⟨Y, ⟨k, x, hxX, hxY⟩, ?_⟩
  rintro Z ⟨l, z, hzX, hzZ⟩
  exact (general_copy_action_compatible G act ranges codes hp hc hInt hMul i k l hxX hxY hzX hzZ).symm

/-- Group laws and graph preservation for copy transitions; existence of
    their source codes is a separate, explicitly supplied premise here. -/
theorem general_copy_graph_action {I : Type v} (G : ExternalGroupData I)
    {t A S e : U} (act ranges codes rho : I → U)
    (htA : Subset s t A)
    (hp : ∀ i, MembershipIsoCode s t t (act i))
    (hc : ∀ i, CopyCode s t A (act i) (ranges i) (codes i))
    (hS : ∀ X, s X S ↔ ∃ i, s X (ranges i))
    (hId : ∀ x y, CodedRelation s (codes G.one) x y ↔ s x A ∧ y = x)
    (hClosed : ∀ i, GraphClosedCode s S e (ranges i))
    (hEdges : ∀ i x y X Y, CodedRelation s (codes i) x X → CodedRelation s (codes i) y Y →
      (CodedRelation s e X Y ↔ s y x))
    (hr : ∀ i, FunctionCode s S (rho i) ∧ ∀ X Y, CodedRelation s (rho i) X Y ↔
      ∃ k x, CodedRelation s (codes k) x X ∧ CodedRelation s (codes (G.mul i k)) x Y) :
    (∀ i, GraphIsoCode s S e S e (rho i)) ∧
      (∀ X Y, CodedRelation s (rho G.one) X Y → X = Y) ∧
      (∀ i j X Z, CodedRelation s (rho (G.mul i j)) X Z ↔
        ∃ Y, CodedRelation s (rho j) X Y ∧ CodedRelation s (rho i) Y Z) ∧
      (∀ i x y, CodedRelation s (act i) x y → CodedRelation s (rho i) x y) := by
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
        by simpa only [external_group_right_inverse] using hxY⟩
    · intro hXY
      obtain ⟨k, x, hxX, hxY⟩ := (hR i X Y).mp hXY
      exact (hR (G.inv i) Y X).mpr ⟨G.mul i k, x, hxY,
        by simpa only [external_group_left_inverse] using hxX⟩
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
  refine ⟨hIso, ?_, ?_, ?_⟩
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

end FullBridge
