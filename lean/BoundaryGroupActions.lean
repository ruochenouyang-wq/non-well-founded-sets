import BoundaryActionCodes
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

theorem boundary_group_action (base : BaseCollection s) {I : Type v} (G : ExternalGroupData I)
    {D N E b A : U} {K : BoundaryRenaming s D N b A}
    (F : BoundaryGraphAttachment s D N E b A K) (hA : TransitiveCode s A) (p q : I → U)
    (hp : ∀ i, MembershipIsoCode s A A (p i)) (hq : ∀ i, GraphIsoCode s N E N E (q i))
    (hOld : ∀ x X, CodedRelation s b x X → s X A)
    (hcomp : ∀ i, BoundaryActionCompatible s b (p i) (q i))
    (hpOne : ∀ x y, CodedRelation s (p G.one) x y → x = y)
    (hqOne : ∀ x y, CodedRelation s (q G.one) x y → x = y)
    (hpMul : ∀ i j x z, CodedRelation s (p (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (p j) x y ∧ CodedRelation s (p i) y z)
    (hqMul : ∀ i j x z, CodedRelation s (q (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (q j) x y ∧ CodedRelation s (q i) y z) :
    ∃ rho : I → U,
      (∀ i, GraphIsoCode s F.domain F.edge F.domain F.edge (rho i)) ∧
      (∀ i X Y, CodedRelation s (rho i) X Y ↔ AttachmentActionRel s (p i) (q i) K.code X Y) ∧
      (∀ X Y, CodedRelation s (rho G.one) X Y → X = Y) ∧
      (∀ i j X Z, CodedRelation s (rho (G.mul i j)) X Z ↔
        ∃ Y, CodedRelation s (rho j) X Y ∧ CodedRelation s (rho i) Y Z) := by
  classical
  have hex := fun i => boundary_action_function base F (hp i) (hq i) hOld (hcomp i)
  let rho : I → U := fun i => Classical.choose (hex i)
  have hf := fun i => (Classical.choose_spec (hex i)).1
  have hr := fun i => (Classical.choose_spec (hex i)).2
  have htarg : ∀ i X Y, CodedRelation s (rho i) X Y → s Y F.domain := by
    intro i X Y h
    apply (F.members Y).mpr
    rcases (hr i X Y).mp h with h | ⟨x, y, _, _, hyY⟩
    · exact Or.inl (((hp i).2.2.1 Y).mpr ⟨X, coded_function_domain (hp i).1 h, h⟩)
    · exact Or.inr ((K.range Y).mpr ⟨y, coded_function_domain K.function hyY, hyY⟩)
  have hOne : ∀ X Y, CodedRelation s (rho G.one) X Y → X = Y := by
    intro X Y h
    rcases (hr G.one X Y).mp h with h | ⟨x, y, hxX, hxy, hyY⟩
    · exact hpOne X Y h
    · have hxy' := hqOne x y hxy
      exact coded_function_value_unique K.function hxX (hxy'.symm ▸ hyY)
  have hMulF : ∀ i j X Z, CodedRelation s (rho (G.mul i j)) X Z →
      ∃ Y, CodedRelation s (rho j) X Y ∧ CodedRelation s (rho i) Y Z := by
    intro i j X Z h
    rcases (hr (G.mul i j) X Z).mp h with h | ⟨x, z, hxX, hxz, hzZ⟩
    · obtain ⟨Y, hXY, hYZ⟩ := (hpMul i j X Z).mp h
      exact ⟨Y, (hr j X Y).mpr (Or.inl hXY), (hr i Y Z).mpr (Or.inl hYZ)⟩
    · obtain ⟨y, hxy, hyz⟩ := (hqMul i j x z).mp hxz
      obtain ⟨Y, hyY, _⟩ := K.function.2 y (graph_iso_value (hq j) hxy)
      exact ⟨Y, (hr j X Y).mpr (Or.inr ⟨x, y, hxX, hxy, hyY⟩),
        (hr i Y Z).mpr (Or.inr ⟨y, z, hyY, hyz, hzZ⟩)⟩
  have hMul : ∀ i j X Z, CodedRelation s (rho (G.mul i j)) X Z ↔
      ∃ Y, CodedRelation s (rho j) X Y ∧ CodedRelation s (rho i) Y Z := by
    intro i j X Z
    refine ⟨hMulF i j X Z, ?_⟩
    rintro ⟨Y, hXY, hYZ⟩
    obtain ⟨Z', hXZ', _⟩ := (hf (G.mul i j)).2 X (coded_function_domain (hf j) hXY)
    obtain ⟨Y', hXY', hY'Z'⟩ := hMulF i j X Z' hXZ'
    have hY := coded_function_value_unique (hf j) hXY' hXY
    have hZ := coded_function_value_unique (hf i) (hY ▸ hY'Z') hYZ
    exact hZ ▸ hXZ'
  have hEdge : ∀ i X Y X' Y', CodedRelation s (rho i) X X' → CodedRelation s (rho i) Y Y' →
      CodedRelation s F.edge X Y → CodedRelation s F.edge X' Y' := by
    intro i X Y X' Y' hXX' hYY' hXY
    rcases (F.members X).mp (coded_function_domain (hf i) hXX') with hXA | hXB
    · have hYX := (F.old.2 X hXA Y).mp hXY
      have hYA : s Y A := hA X hXA Y hYX
      have hx := (boundary_action_old K (hp i) (hcomp i) hXA).mp ((hr i X X').mp hXX')
      have hy := (boundary_action_old K (hp i) (hcomp i) hYA).mp ((hr i Y Y').mp hYY')
      have hX'A := ((hp i).2.2.1 X').mpr ⟨X, hXA, hx⟩
      exact (F.old.2 X' hX'A Y').mpr ((hp i).2.2.2 X Y X' Y' hx hy |>.mp hYX)
    · obtain ⟨x, _, hxX⟩ := (K.range X).mp hXB
      obtain ⟨y, hxy, hyY⟩ := (F.rows x X hxX Y).mp hXY
      obtain ⟨x', hxx', hx'X'⟩ := (boundary_action_copy K (hp i) (hq i) hOld (hcomp i) hxX).mp
        ((hr i X X').mp hXX')
      obtain ⟨y', hyy', hy'Y'⟩ := (boundary_action_copy K (hp i) (hq i) hOld (hcomp i) hyY).mp
        ((hr i Y Y').mp hYY')
      exact (F.rows x' X' hx'X' Y').mpr ⟨y',
        (hq i).2.2.2 x y x' y' hxx' hyy' |>.mp hxy, hy'Y'⟩
  exact ⟨rho, coded_group_graph_isomorphisms G rho hf htarg hOne hMul hEdge, hr, hOne, hMul⟩


#print axioms boundary_group_action
end FullBridge
