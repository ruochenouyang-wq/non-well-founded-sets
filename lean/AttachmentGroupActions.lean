import AttachmentActionCodes
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

theorem coded_group_graph_isomorphisms {I : Type v} (G : ExternalGroupData I) {S e : U}
    (rho : I → U) (hf : ∀ i, FunctionCode s S (rho i))
    (htarget : ∀ i x y, CodedRelation s (rho i) x y → s y S)
    (hOne : ∀ x y, CodedRelation s (rho G.one) x y → x = y)
    (hMul : ∀ i j x z, CodedRelation s (rho (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (rho j) x y ∧ CodedRelation s (rho i) y z)
    (hEdge : ∀ i x y X Y, CodedRelation s (rho i) x X → CodedRelation s (rho i) y Y →
      CodedRelation s e x y → CodedRelation s e X Y) :
    ∀ i, GraphIsoCode s S e S e (rho i) := by
  have hinv : ∀ i x y, CodedRelation s (rho i) x y → CodedRelation s (rho (G.inv i)) y x := by
    intro i x y hxy
    obtain ⟨z, hyz, _⟩ := (hf (G.inv i)).2 y (htarget i x y hxy)
    have hxz := (hMul (G.inv i) i x z).mpr ⟨y, hxy, hyz⟩
    rw [G.inv_mul] at hxz
    exact (hOne x z hxz).symm ▸ hyz
  intro i
  refine ⟨hf i, ?_, ?_, ?_⟩
  · intro x y z hxz hyz
    exact coded_function_value_unique (hf (G.inv i)) (hinv i x z hxz) (hinv i y z hyz)
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hyx, _⟩ := (hf (G.inv i)).2 y hy
      have hx := htarget (G.inv i) y x hyx
      obtain ⟨z, hxz, _⟩ := (hf i).2 x hx
      have hyz := (hMul i (G.inv i) y z).mpr ⟨x, hyx, hxz⟩
      rw [G.mul_inv] at hyz
      exact ⟨x, hx, (hOne y z hyz).symm ▸ hxz⟩
    · exact fun ⟨x, _, hxy⟩ => htarget i x y hxy
  · intro x y X Y hx hy
    exact ⟨hEdge i x y X Y hx hy,
      hEdge (G.inv i) X Y x y (hinv i x X hx) (hinv i y Y hy)⟩

theorem attachment_group_action (base : BaseCollection s) {I : Type v} (G : ExternalGroupData I)
    {t A a r : U} (D : MemberGraphAttachment s t A a r) (hA : TransitiveCode s A) (p q : I → U)
    (hp : ∀ i, MembershipIsoCode s A A (p i)) (hq : ∀ i, GraphIsoCode s a r a r (q i))
    (hstable : ∀ i x y, s x t → CodedRelation s (p i) x y → s y t)
    (hag : ∀ i x y, s x t → (CodedRelation s (p i) x y ↔ CodedRelation s (q i) x y))
    (hpOne : ∀ x y, CodedRelation s (p G.one) x y → x = y)
    (hqOne : ∀ x y, CodedRelation s (q G.one) x y → x = y)
    (hpMul : ∀ i j x z, CodedRelation s (p (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (p j) x y ∧ CodedRelation s (p i) y z)
    (hqMul : ∀ i j x z, CodedRelation s (q (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (q j) x y ∧ CodedRelation s (q i) y z) :
    ∃ rho : I → U,
      (∀ i, GraphIsoCode s D.domain D.edge D.domain D.edge (rho i)) ∧
      (∀ i X Y, CodedRelation s (rho i) X Y ↔ AttachmentActionRel s (p i) (q i) D.copy X Y) ∧
      (∀ X Y, CodedRelation s (rho G.one) X Y → X = Y) ∧
      (∀ i j X Z, CodedRelation s (rho (G.mul i j)) X Z ↔
        ∃ Y, CodedRelation s (rho j) X Y ∧ CodedRelation s (rho i) Y Z) := by
  classical
  have hex := fun i => attachment_action_function base D (hp i) (hq i) (hstable i) (hag i)
  let rho : I → U := fun i => Classical.choose (hex i)
  have hf := fun i => (Classical.choose_spec (hex i)).1
  have hr := fun i => (Classical.choose_spec (hex i)).2
  have htarg : ∀ i X Y, CodedRelation s (rho i) X Y → s Y D.domain := by
    intro i X Y h
    apply (D.members Y).mpr
    rcases (hr i X Y).mp h with h | ⟨x, y, _, _, hyY⟩
    · exact Or.inl (((hp i).2.2.1 Y).mpr ⟨X, coded_function_domain (hp i).1 h, h⟩)
    · exact Or.inr ((D.copyRange Y).mpr ⟨y, coded_function_domain D.copyFunction hyY, hyY⟩)
  have hOne : ∀ X Y, CodedRelation s (rho G.one) X Y → X = Y := by
    intro X Y h
    rcases (hr G.one X Y).mp h with h | ⟨x, y, hxX, hxy, hyY⟩
    · exact hpOne X Y h
    · have hxy' := hqOne x y hxy
      exact coded_function_value_unique D.copyFunction hxX (hxy'.symm ▸ hyY)
  have hMulF : ∀ i j X Z, CodedRelation s (rho (G.mul i j)) X Z →
      ∃ Y, CodedRelation s (rho j) X Y ∧ CodedRelation s (rho i) Y Z := by
    intro i j X Z h
    rcases (hr (G.mul i j) X Z).mp h with h | ⟨x, z, hxX, hxz, hzZ⟩
    · obtain ⟨Y, hXY, hYZ⟩ := (hpMul i j X Z).mp h
      exact ⟨Y, (hr j X Y).mpr (Or.inl hXY), (hr i Y Z).mpr (Or.inl hYZ)⟩
    · obtain ⟨y, hxy, hyz⟩ := (hqMul i j x z).mp hxz
      obtain ⟨Y, hyY, _⟩ := D.copyFunction.2 y (graph_iso_value (hq j) hxy)
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
      CodedRelation s D.edge X Y → CodedRelation s D.edge X' Y' := by
    intro i X Y X' Y' hXX' hYY' hXY
    rcases (D.members X).mp (coded_function_domain (hf i) hXX') with hXA | hXB
    · have hYX := (D.old.2 X hXA Y).mp hXY
      have hYA : s Y A := hA X hXA Y hYX
      have hx := (attachment_action_old D (hp i) (hq i) (hstable i) (hag i) hXA).mp ((hr i X X').mp hXX')
      have hy := (attachment_action_old D (hp i) (hq i) (hstable i) (hag i) hYA).mp ((hr i Y Y').mp hYY')
      have hX'A := ((hp i).2.2.1 X').mpr ⟨X, hXA, hx⟩
      exact (D.old.2 X' hX'A Y').mpr ((hp i).2.2.2 X Y X' Y' hx hy |>.mp hYX)
    · obtain ⟨x, _, hxX⟩ := (D.copyRange X).mp hXB
      obtain ⟨y, _, hyY⟩ := (D.copyRange Y).mp (D.closed.2 X hXB Y hXY)
      obtain ⟨x', hxx', hx'X'⟩ := (attachment_action_copy D (hp i) (hq i) (hstable i) (hag i) hxX).mp
        ((hr i X X').mp hXX')
      obtain ⟨y', hyy', hy'Y'⟩ := (attachment_action_copy D (hp i) (hq i) (hstable i) (hag i) hyY).mp
        ((hr i Y Y').mp hYY')
      exact (D.transported x' y' X' Y' hx'X' hy'Y').mpr
        ((hq i).2.2.2 x y x' y' hxx' hyy' |>.mp ((D.transported x y X Y hxX hyY).mp hXY))
  exact ⟨rho, coded_group_graph_isomorphisms G rho hf htarg hOne hMul hEdge, hr, hOne, hMul⟩

#print axioms attachment_group_action
end FullBridge
