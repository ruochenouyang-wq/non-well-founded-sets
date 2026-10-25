import ActionFamilyBoundaries
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem family_boundary_tag_injective {O A N E p x y X Y Z : U}
    (B : ActionFamilyBoundary s O A N E) (K : BoundaryRenaming s B.domain N B.code A)
    (hX : IsOrderedPair s X p x) (hY : IsOrderedPair s Y p y)
    (hx : CodedRelation s K.code X Z) (hy : CodedRelation s K.code Y Z) : x = y := by
  rcases K.collision X Y Z hx hy with h | ⟨hx, hy⟩
  · exact (orderedPair_injective (h ▸ hX) hY).2
  · obtain ⟨_, _, _, _, _, _, _, hx⟩ := (B.values X Z).mp hx
    obtain ⟨_, _, _, _, _, _, _, hy⟩ := (B.values Y Z).mp hy
    exact (orderedPair_injective hX hx).2.trans (orderedPair_injective hY hy).2.symm

/-- One tagged membership component remains a closed extensional copy after
    gluing all common parameters. No distinctness between components is needed. -/
theorem action_family_attached_component (base : BaseCollection s) {w O N E p : U}
    (P Q : CodedMaskAction base w) (hp : s p O) (hQ : ActionFamilyMember base p Q)
    (hN : ∀ X, s X N ↔ OrbitDiagramNode s O X)
    (hE : ∀ X Y, CodedRelation s E X Y ↔ FamilyDiagramEdge s O X Y)
    (B : ActionFamilyBoundary s O P.domain N E)
    (K : BoundaryRenaming s B.domain N B.code P.domain)
    (F : BoundaryGraphAttachment s B.domain N E B.code P.domain K) :
    ∃ e, ∃ C : ClosedGraphCopy s F.domain F.edge Q.domain e,
      (∀ x y, CodedRelation s e x y ↔ s x Q.domain ∧ s y x) ∧
      ∀ x X, CodedRelation s C.code x X ↔ s x Q.domain ∧
        ∃ u, IsOrderedPair s u p x ∧ CodedRelation s K.code u X := by
  obtain ⟨t, ht⟩ := hQ
  obtain ⟨k, hk, hkr⟩ := definable_function_code base (orderedPairFormula (n := 3) 0 2 1)
    (cons p Fin.elim0) Q.domain (by
      intro x _
      obtain ⟨X, hX⟩ := orderedPair_exists base.pairing p x
      exact ⟨X, (eval_orderedPairFormula s 0 2 1 _).mpr hX,
        fun Y hY => orderedPair_unique base.extensional ((eval_orderedPairFormula s 0 2 1 _).mp hY) hX⟩)
  have hkpair : ∀ x X, CodedRelation s k x X ↔ s x Q.domain ∧ IsOrderedPair s X p x :=
    fun x X => (hkr x X).trans (and_congr Iff.rfl (eval_orderedPairFormula s 0 2 1 _))
  have hkN : ∀ x X, CodedRelation s k x X → s X N := by
    intro x X hx
    obtain ⟨hx, hX⟩ := (hkpair x X).mp hx
    exact (hN X).mpr ⟨p, t, Q.domain, Q.family, x, hp, ht, hx, hX⟩
  obtain ⟨f, hf, hfr⟩ := coded_functions_compose base hk K.function hkN
  have hv : ∀ x X, CodedRelation s f x X ↔ s x Q.domain ∧
      ∃ u, IsOrderedPair s u p x ∧ CodedRelation s K.code u X := by
    intro x X
    rw [hfr]
    constructor
    · rintro ⟨u, hxu, huX⟩
      exact ⟨((hkpair x u).mp hxu).1, u, ((hkpair x u).mp hxu).2, huX⟩
    · rintro ⟨hx, u, hxu, huX⟩
      exact ⟨u, (hkpair x u).mpr ⟨hx, hxu⟩, huX⟩
  have hfi : InjectiveCode s f := by
    intro x y Z hx hy
    obtain ⟨_, u, hxu, huZ⟩ := (hv x Z).mp hx
    obtain ⟨_, v, hyv, hvZ⟩ := (hv y Z).mp hy
    exact family_boundary_tag_injective B K hxu hyv huZ hvZ
  obtain ⟨d, hd⟩ := coded_image_set_exists base f Q.domain
  have hclosed : GraphClosedCode s F.domain F.edge d := by
    constructor
    · intro X hX
      obtain ⟨x, _, hxX⟩ := (hd X).mp hX
      obtain ⟨_, u, _, huX⟩ := (hv x X).mp hxX
      exact F.closed.1 X ((K.range X).mpr ⟨u, coded_function_domain K.function huX, huX⟩)
    · intro X hX Y hXY
      obtain ⟨x, hx, hxX⟩ := (hd X).mp hX
      obtain ⟨_, u, hxu, huX⟩ := (hv x X).mp hxX
      obtain ⟨v, huv, hvY⟩ := (F.rows u X huX Y).mp hXY
      obtain ⟨y, hyv, _, hyx⟩ := (family_diagram_edge_from base Q hp ⟨t, ht⟩ hxu).mp ((hE u v).mp huv)
      have hy := Q.transitive x hx y hyx
      exact (hd Y).mpr ⟨y, hy, (hv y Y).mpr ⟨hy, v, hyv, hvY⟩⟩
  have htransport : ∀ x y X Y, CodedRelation s f x X → CodedRelation s f y Y →
      (CodedRelation s F.edge X Y ↔ s y x) := by
    intro x y X Y hxX hyY
    obtain ⟨hx, u, hxu, huX⟩ := (hv x X).mp hxX
    obtain ⟨_, v, hyv, hvY⟩ := (hv y Y).mp hyY
    constructor
    · intro hXY
      obtain ⟨v', huv', hv'Y⟩ := (F.rows u X huX Y).mp hXY
      obtain ⟨z, hzv, _, hzx⟩ := (family_diagram_edge_from base Q hp ⟨t, ht⟩ hxu).mp ((hE u v').mp huv')
      exact (family_boundary_tag_injective B K hzv hyv hv'Y hvY) ▸ hzx
    · intro hyx
      exact (F.rows u X huX Y).mpr ⟨v,
        (hE u v).mpr ((family_diagram_edge_iff base Q hp ⟨t, ht⟩ hxu hyv).mpr ⟨hx, hyx⟩), hvY⟩
  have hext : GraphExtensionalCode s d F.edge := by
    intro X hX Y hY hrows
    obtain ⟨x, hx, hxX⟩ := (hd X).mp hX
    obtain ⟨y, hy, hyY⟩ := (hd Y).mp hY
    have hxy : x = y := by
      apply base.extensional
      intro z
      have hz : s z Q.domain → (s z x ↔ s z y) := by
        intro hz
        obtain ⟨Z, hzZ, _⟩ := hf.2 z hz
        exact (htransport x z X Z hxX hzZ).symm.trans
          ((hrows Z ((hd Z).mpr ⟨z, hz, hzZ⟩)).trans (htransport y z Y Z hyY hzZ))
      exact ⟨fun hzx => (hz (Q.transitive x hx z hzx)).mp hzx,
        fun hzy => (hz (Q.transitive y hy z hzy)).mpr hzy⟩
    exact coded_function_value_unique hf (hxy ▸ hxX) hyY
  obtain ⟨e, _, _, _, he, _⟩ := membership_graph_identity_decoration base Q.transitive
  refine ⟨e, ⟨d, f, hf, hfi, hd, hclosed, ?_, hext⟩, he, hv⟩
  intro x y X Y hxX hyY
  exact (htransport x y X Y hxX hyY).trans
    ⟨fun h => (he x y).mpr ⟨coded_function_domain hf hxX, h⟩, fun h => ((he x y).mp h).2⟩

#print axioms action_family_attached_component
end FullBridge
