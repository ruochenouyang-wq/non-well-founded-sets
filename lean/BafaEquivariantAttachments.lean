import AttachmentGroupActions
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

theorem attachment_decoration_pullback (base : BaseCollection s) {t A a r g : U}
    (D : MemberGraphAttachment s t A a r) (hG : GraphCode s a r)
    (hg : DecorationCode s D.domain D.edge g) :
    ∃ f, DecorationCode s a r f ∧ ∀ x X, CodedRelation s f x X ↔
      ∃ u, CodedRelation s D.copy x u ∧ CodedRelation s g u X := by
  have hkD : ∀ x u, CodedRelation s D.copy x u → s u D.domain := fun x u h =>
    D.closed.1 u ((D.copyRange u).mpr ⟨x, coded_function_domain D.copyFunction h, h⟩)
  obtain ⟨f, hf, hfr⟩ := coded_functions_compose base D.copyFunction hg.1 hkD
  refine ⟨f, ⟨hf, ?_⟩, hfr⟩
  intro x hx X hxX Y
  obtain ⟨u, hxu, huX⟩ := (hfr x X).mp hxX
  constructor
  · intro hYX
    obtain ⟨v, _, huv, hvY⟩ := (hg.2 u (hkD x u hxu) X huX Y).mp hYX
    have huB := (D.copyRange u).mpr ⟨x, hx, hxu⟩
    obtain ⟨y, hy, hyv⟩ := (D.copyRange v).mp (D.closed.2 u huB v huv)
    exact ⟨y, hy, (D.transported x y u v hxu hyv).mp huv, (hfr y Y).mpr ⟨v, hyv, hvY⟩⟩
  · rintro ⟨y, _, hxy, hyY⟩
    obtain ⟨v, hyv, hvY⟩ := (hfr y Y).mp hyY
    exact (hg.2 u (hkD x u hxu) X huX Y).mpr
      ⟨v, hkD y v hyv, (D.transported x y u v hxu hyv).mpr hxy, hvY⟩

/-- A genuine equivariant fixed-part extension, with an injective solution of
    the supplied extensional graph. No finiteness assumption on the group. -/
theorem bafa_equivariant_graph_attachment (base : BaseCollection s) (hBafa : BAFACode s)
    {I : Type v} (G : ExternalGroupData I) {t A a r : U}
    (ht : TransitiveCode s t) (hA : TransitiveCode s A) (htA : Subset s t A)
    (hG : GraphCode s a r) (hExt : GraphExtensionalCode s a r) (hEnd : EndExtensionCode s a r t)
    (p q : I → U) (hp : ∀ i, MembershipIsoCode s A A (p i))
    (hq : ∀ i, GraphIsoCode s a r a r (q i))
    (hstable : ∀ i x y, s x t → CodedRelation s (p i) x y → s y t)
    (hag : ∀ i x y, s x t → (CodedRelation s (p i) x y ↔ CodedRelation s (q i) x y))
    (hpOne : ∀ x y, CodedRelation s (p G.one) x y → x = y)
    (hqOne : ∀ x y, CodedRelation s (q G.one) x y → x = y)
    (hpMul : ∀ i j x z, CodedRelation s (p (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (p j) x y ∧ CodedRelation s (p i) y z)
    (hqMul : ∀ i j x z, CodedRelation s (q (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (q j) x y ∧ CodedRelation s (q i) y z) :
    ∃ T f, ∃ out : I → U, TransitiveCode s T ∧ Subset s A T ∧
      DecorationCode s a r f ∧ InjectiveCode s f ∧
      (∀ x, s x t → CodedRelation s f x x) ∧
      (∀ x X, CodedRelation s f x X → s X T) ∧
      (∀ i, MembershipIsoCode s T T (out i)) ∧
      (∀ X Y, CodedRelation s (out G.one) X Y → X = Y) ∧
      (∀ i j X Z, CodedRelation s (out (G.mul i j)) X Z ↔
        ∃ Y, CodedRelation s (out j) X Y ∧ CodedRelation s (out i) Y Z) ∧
      (∀ i x y, CodedRelation s (p i) x y → CodedRelation s (out i) x y) ∧
      (∀ i x y X Y, CodedRelation s (q i) x y → CodedRelation s f x X →
        CodedRelation s f y Y → CodedRelation s (out i) X Y) := by
  obtain ⟨D⟩ := member_graph_attachment_exists base ht hA htA hG hEnd
  obtain ⟨rho, hrho, hr, hrOne, hrMul⟩ := attachment_group_action base G D hA p q hp hq
    hstable hag hpOne hqOne hpMul hqMul
  obtain ⟨m, g, T, out, hm, hg, hT, hgT, hAT, hfix, hker, hout, hOne, hMul, hOld, _⟩ :=
    bafa_fixed_coherent_realization base hBafa G.one G.mul rho hA D.graph D.old hrho hrOne hrMul
  obtain ⟨f, hf, hfr⟩ := attachment_decoration_pullback base D hG hg
  refine ⟨T, f, out, hT, hAT, hf, ?_, ?_, ?_, fun i => (hout i).1, hOne, hMul, ?_, ?_⟩
  · intro x y Z hxZ hyZ
    obtain ⟨X, hxX, hXZ⟩ := (hfr x Z).mp hxZ
    obtain ⟨Y, hyY, hYZ⟩ := (hfr y Z).mp hyZ
    have hXB := (D.copyRange X).mpr ⟨x, coded_function_domain D.copyFunction hxX, hxX⟩
    have hYB := (D.copyRange Y).mpr ⟨y, coded_function_domain D.copyFunction hyY, hyY⟩
    have hXY := least_relation_preserves_closed_extensional base D.closed
      (attachment_closed_extensional D hExt) hm hXB hYB ((hker X Y Z Z hXZ hYZ).mp rfl)
    exact D.copyInjective x y Y (hXY ▸ hxX) hyY
  · intro x hx
    exact (hfr x x).mpr ⟨x, D.fixed x hx, hfix x (htA x hx)⟩
  · intro x X hxX
    obtain ⟨u, _, huX⟩ := (hfr x X).mp hxX
    exact (hgT X).mpr ⟨u, coded_function_domain hg.1 huX, huX⟩
  · intro i x y hxy
    exact hOld i x y (coded_function_domain (hp i).1 hxy)
      (((hp i).2.2.1 y).mpr ⟨x, coded_function_domain (hp i).1 hxy, hxy⟩)
      ((hr i x y).mpr (Or.inl hxy))
  · intro i x y X Y hxy hxX hyY
    obtain ⟨u, hxu, huX⟩ := (hfr x X).mp hxX
    obtain ⟨v, hyv, hvY⟩ := (hfr y Y).mp hyY
    exact ((hout i).2 X Y).mpr ⟨u, v, huX, (hr i u v).mpr (Or.inr ⟨x, y, hxu, hxy, hyv⟩), hvY⟩

#print axioms bafa_equivariant_graph_attachment
end FullBridge
