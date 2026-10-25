import ActionFamilyDiagrams
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem action_family_node (base : BaseCollection s) {w O X : U}
    (h : ActionFamilyCode base w O) (hx : OrbitDiagramNode s O X) :
    ∃ p, ∃ Q : CodedMaskAction base w, ∃ x,
      s p O ∧ ActionFamilyMember base p Q ∧ s x Q.domain ∧ IsOrderedPair s X p x := by
  obtain ⟨p, t, D, K, x, hp, hc, hx, hX⟩ := hx
  obtain ⟨Q, rfl, rfl⟩ := action_family_parameters base h hp hc
  exact ⟨p, Q, x, hp, ⟨t, hc⟩, hx, hX⟩

theorem family_diagram_move_from (base : BaseCollection s) {w O p x X Y : U}
    (Q : CodedMaskAction base w) (i : InternalMask s w) (hp : s p O)
    (hQ : ActionFamilyMember base p Q) (hX : IsOrderedPair s X p x) :
    FamilyDiagramMove s O i.val X Y ↔
      ∃ y, IsOrderedPair s Y p y ∧ CodedRelation s (Q.maps i) x y := by
  constructor
  · intro h
    have hh := h
    obtain ⟨q, t, D, K, u, v, _, _, hXu, hYv, _⟩ := h
    obtain ⟨rfl, rfl⟩ := orderedPair_injective hXu hX
    exact ⟨v, hYv, (family_diagram_move_iff base Q i hp hQ hX hYv).mp hh⟩
  · rintro ⟨y, hY, hxy⟩
    exact (family_diagram_move_iff base Q i hp hQ hX hY).mpr hxy

theorem family_diagram_move_to (base : BaseCollection s) {w O p y X Y : U}
    (Q : CodedMaskAction base w) (i : InternalMask s w) (hp : s p O)
    (hQ : ActionFamilyMember base p Q) (hY : IsOrderedPair s Y p y) :
    FamilyDiagramMove s O i.val X Y ↔
      ∃ x, IsOrderedPair s X p x ∧ CodedRelation s (Q.maps i) x y := by
  constructor
  · intro h
    have hh := h
    obtain ⟨q, t, D, K, u, v, _, _, hXu, hYv, _⟩ := h
    obtain ⟨rfl, rfl⟩ := orderedPair_injective hYv hY
    exact ⟨u, hXu, (family_diagram_move_iff base Q i hp hQ hXu hY).mp hh⟩
  · rintro ⟨x, hX, hxy⟩
    exact (family_diagram_move_iff base Q i hp hQ hX hY).mpr hxy

theorem family_diagram_move_nodes (base : BaseCollection s) {w O X Y : U}
    (h : ActionFamilyCode base w O) (i : InternalMask s w)
    (hm : FamilyDiagramMove s O i.val X Y) : OrbitDiagramNode s O X ∧ OrbitDiagramNode s O Y := by
  obtain ⟨p, t, D, K, x, y, hp, hpar, hX, hY, hm⟩ := hm
  obtain ⟨Q, rfl, rfl⟩ := action_family_parameters base h hp hpar
  have hxy := (action_family_point_iff base Q i).mp hm
  have hx := coded_function_domain (Q.iso i).1 hxy
  have hy := ((Q.iso i).2.2.1 y).mpr ⟨x, hx, hxy⟩
  exact ⟨⟨p, t, Q.domain, Q.family, x, hp, hpar, hx, hX⟩,
    ⟨p, t, Q.domain, Q.family, y, hp, hpar, hy, hY⟩⟩

theorem family_diagram_move_total_unique (base : BaseCollection s) {w O X : U}
    (h : ActionFamilyCode base w O) (i : InternalMask s w) (hX : OrbitDiagramNode s O X) :
    ∃ Y, FamilyDiagramMove s O i.val X Y ∧ ∀ Z, FamilyDiagramMove s O i.val X Z → Z = Y := by
  obtain ⟨p, Q, x, hp, hQ, hx, hpair⟩ := action_family_node base h hX
  obtain ⟨y, hxy, _⟩ := (Q.iso i).1.2 x hx
  obtain ⟨Y, hY⟩ := orderedPair_exists base.pairing p y
  refine ⟨Y, (family_diagram_move_iff base Q i hp hQ hpair hY).mpr hxy, ?_⟩
  intro Z hZ
  obtain ⟨z, hZz, hxz⟩ := (family_diagram_move_from base Q i hp hQ hpair).mp hZ
  have hz := coded_function_value_unique (Q.iso i).1 hxz hxy
  exact orderedPair_unique base.extensional (hz ▸ hZz) hY

theorem family_diagram_move_injective (base : BaseCollection s) {w O X Y Z : U}
    (h : ActionFamilyCode base w O) (i : InternalMask s w)
    (hX : FamilyDiagramMove s O i.val X Z) (hY : FamilyDiagramMove s O i.val Y Z) : X = Y := by
  obtain ⟨p, Q, z, hp, hQ, _, hZ⟩ := action_family_node base h (family_diagram_move_nodes base h i hX).2
  obtain ⟨x, hx, hxz⟩ := (family_diagram_move_to base Q i hp hQ hZ).mp hX
  obtain ⟨y, hy, hyz⟩ := (family_diagram_move_to base Q i hp hQ hZ).mp hY
  have hxy := (Q.iso i).2.1 x y z hxz hyz
  exact orderedPair_unique base.extensional (hxy ▸ hx) hy

theorem family_diagram_move_surjective (base : BaseCollection s) {w O Y : U}
    (h : ActionFamilyCode base w O) (i : InternalMask s w) (hY : OrbitDiagramNode s O Y) :
    ∃ X, OrbitDiagramNode s O X ∧ FamilyDiagramMove s O i.val X Y := by
  obtain ⟨p, Q, y, hp, hQ, hy, hY⟩ := action_family_node base h hY
  obtain ⟨x, _, hxy⟩ := ((Q.iso i).2.2.1 y).mp hy
  obtain ⟨X, hX⟩ := orderedPair_exists base.pairing p x
  have hmove := (family_diagram_move_iff base Q i hp hQ hX hY).mpr hxy
  exact ⟨X, (family_diagram_move_nodes base h i hmove).1, hmove⟩

theorem family_diagram_edge_from (base : BaseCollection s) {w O p x X Y : U}
    (Q : CodedMaskAction base w) (hp : s p O) (hQ : ActionFamilyMember base p Q)
    (hX : IsOrderedPair s X p x) :
    FamilyDiagramEdge s O X Y ↔ ∃ y, IsOrderedPair s Y p y ∧ s x Q.domain ∧ s y x := by
  constructor
  · intro h
    have hh := h
    obtain ⟨q, t, D, K, u, v, _, _, _, hXu, hYv, _⟩ := h
    obtain ⟨rfl, rfl⟩ := orderedPair_injective hXu hX
    exact ⟨v, hYv, (family_diagram_edge_iff base Q hp hQ hX hYv).mp hh⟩
  · rintro ⟨y, hY, hx, hy⟩
    exact (family_diagram_edge_iff base Q hp hQ hX hY).mpr ⟨hx, hy⟩

theorem family_diagram_move_edges (base : BaseCollection s) {w O X Y XX YY : U}
    (h : ActionFamilyCode base w O) (i : InternalMask s w)
    (hX : FamilyDiagramMove s O i.val X XX) (hY : FamilyDiagramMove s O i.val Y YY) :
    FamilyDiagramEdge s O X Y ↔ FamilyDiagramEdge s O XX YY := by
  obtain ⟨p, Q, x, hp, hQ, hx, hPx⟩ := action_family_node base h (family_diagram_move_nodes base h i hX).1
  obtain ⟨xx, hPxx, hxx⟩ := (family_diagram_move_from base Q i hp hQ hPx).mp hX
  have hxxD := ((Q.iso i).2.2.1 xx).mpr ⟨x, hx, hxx⟩
  constructor
  · intro he
    obtain ⟨y, hPy, _, hyx⟩ := (family_diagram_edge_from base Q hp hQ hPx).mp he
    obtain ⟨yy, hPyy, hyy⟩ := (family_diagram_move_from base Q i hp hQ hPy).mp hY
    exact (family_diagram_edge_iff base Q hp hQ hPxx hPyy).mpr
      ⟨hxxD, ((Q.iso i).2.2.2 x y xx yy hxx hyy).mp hyx⟩
  · intro he
    obtain ⟨yy, hPyy, _, hyyxx⟩ := (family_diagram_edge_from base Q hp hQ hPxx).mp he
    obtain ⟨y, hPy, hyy⟩ := (family_diagram_move_to base Q i hp hQ hPyy).mp hY
    exact (family_diagram_edge_iff base Q hp hQ hPx hPy).mpr
      ⟨hx, ((Q.iso i).2.2.2 x y xx yy hxx hyy).mpr hyyxx⟩

theorem family_diagram_move_one (base : BaseCollection s) {w O X Y : U}
    (h : ActionFamilyCode base w O) (hm : FamilyDiagramMove s O (internalMaskOne base w).val X Y) : X = Y := by
  obtain ⟨p, Q, x, hp, hQ, _, hX⟩ := action_family_node base h (family_diagram_move_nodes base h _ hm).1
  obtain ⟨y, hY, hxy⟩ := (family_diagram_move_from base Q _ hp hQ hX).mp hm
  exact orderedPair_unique base.extensional ((Q.one x y hxy) ▸ hX) hY

theorem family_diagram_move_mul (base : BaseCollection s) {w O X Z : U}
    (h : ActionFamilyCode base w O) (i j : InternalMask s w) :
    FamilyDiagramMove s O (internalMaskMul base i j).val X Z ↔
      ∃ Y, FamilyDiagramMove s O j.val X Y ∧ FamilyDiagramMove s O i.val Y Z := by
  constructor
  · intro hm
    obtain ⟨p, Q, x, hp, hQ, _, hX⟩ := action_family_node base h (family_diagram_move_nodes base h _ hm).1
    obtain ⟨z, hZ, hxz⟩ := (family_diagram_move_from base Q _ hp hQ hX).mp hm
    obtain ⟨y, hxy, hyz⟩ := (Q.mul i j x z).mp hxz
    obtain ⟨Y, hY⟩ := orderedPair_exists base.pairing p y
    exact ⟨Y, (family_diagram_move_iff base Q j hp hQ hX hY).mpr hxy,
      (family_diagram_move_iff base Q i hp hQ hY hZ).mpr hyz⟩
  · rintro ⟨Y, hXY, hYZ⟩
    obtain ⟨p, Q, x, hp, hQ, _, hX⟩ := action_family_node base h (family_diagram_move_nodes base h j hXY).1
    obtain ⟨y, hY, hxy⟩ := (family_diagram_move_from base Q j hp hQ hX).mp hXY
    obtain ⟨z, hZ, hyz⟩ := (family_diagram_move_from base Q i hp hQ hY).mp hYZ
    exact (family_diagram_move_iff base Q _ hp hQ hX hZ).mpr ((Q.mul i j x z).mpr ⟨y, hxy, hyz⟩)

#print axioms family_diagram_move_edges
#print axioms family_diagram_move_mul
end FullBridge
