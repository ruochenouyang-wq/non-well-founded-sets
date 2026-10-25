import PartialIsoRelabeling
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem transported_membership_edge_iff {k e : U}
    (hi : InjectiveCode s k)
    (he : ∀ X Y, CodedRelation s e X Y ↔
      ∃ x y, CodedRelation s k x X ∧ CodedRelation s k y Y ∧ s y x)
    {x y X Y : U} (hx : CodedRelation s k x X) (hy : CodedRelation s k y Y) :
    CodedRelation s e X Y ↔ s y x := by
  constructor
  · intro h
    obtain ⟨u, v, hu, hv, hvu⟩ := (he X Y).mp h
    have hux := hi u x X hu hx
    have hvy := hi v y Y hv hy
    exact hux ▸ hvy ▸ hvu
  · intro h
    exact (he X Y).mpr ⟨x, y, hx, hy, h⟩

/-- Transporting a transitive membership graph along an internal bijection
    gives an extensional graph that literally extends the prescribed range. -/
theorem partial_iso_extension_graph (base : BaseCollection s) {a b p A : U}
    (ha : TransitiveCode s a) (hb : TransitiveCode s b)
    (hp : MembershipIsoCode s a b p) (hA : TransitiveCode s A) (haA : Subset s a A) :
    ∃ B k e, FunctionCode s A k ∧ InjectiveCode s k ∧ RangeCode s A k B ∧
      (∀ x y, CodedRelation s p x y → CodedRelation s k x y) ∧
      GraphCode s B e ∧ GraphExtensionalCode s B e ∧ EndExtensionCode s B e b ∧
      ∀ x y X Y, CodedRelation s k x X → CodedRelation s k y Y →
        (CodedRelation s e X Y ↔ s y x) := by
  obtain ⟨B, k, hk, hki, hkr, hbB, hpk, _⟩ := extend_coded_bijection_domain base hp.1 hp.2.1 hp.2.2.1 haA
  obtain ⟨e, heG, he⟩ := transported_membership_graph base hk hkr
  have hEdge := fun {x y X Y} (hx : CodedRelation s k x X) (hy : CodedRelation s k y Y) =>
    transported_membership_edge_iff hki he hx hy
  refine ⟨B, k, e, hk, hki, hkr, hpk, heG, ?_, ⟨hbB, ?_⟩, fun _ _ _ _ hx hy => hEdge hx hy⟩
  · intro X hX Y hY hrows
    obtain ⟨x, hx, hxX⟩ := (hkr X).mp hX
    obtain ⟨y, hy, hyY⟩ := (hkr Y).mp hY
    have hxy : x = y := by
      apply base.extensional
      intro z
      constructor
      · intro hzx
        obtain ⟨Z, hzZ, _⟩ := hk.2 z (hA x hx z hzx)
        have hZ := (hkr Z).mpr ⟨z, hA x hx z hzx, hzZ⟩
        exact (hEdge hyY hzZ).mp ((hrows Z hZ).mp ((hEdge hxX hzZ).mpr hzx))
      · intro hzy
        obtain ⟨Z, hzZ, _⟩ := hk.2 z (hA y hy z hzy)
        have hZ := (hkr Z).mpr ⟨z, hA y hy z hzy, hzZ⟩
        exact (hEdge hxX hzZ).mp ((hrows Z hZ).mpr ((hEdge hyY hzZ).mpr hzy))
    exact coded_function_value_unique hk hxX (hxy.symm ▸ hyY)
  · intro X hX Y
    obtain ⟨x, hx, hxX⟩ := (hp.2.2.1 X).mp hX
    constructor
    · intro hXY
      obtain ⟨u, v, huX, hvY, hvu⟩ := (he X Y).mp hXY
      have hux := hki u x X huX (hpk x X hxX)
      have hvx : s v x := hux ▸ hvu
      have hva := ha x hx v hvx
      obtain ⟨V, hvV, _⟩ := hp.1.2 v hva
      have hVY := coded_function_value_unique hk (hpk v V hvV) hvY
      exact hVY ▸ (hp.2.2.2 x v X V hxX hvV).mp hvx
    · intro hYX
      obtain ⟨y, _, hyY⟩ := (hp.2.2.1 Y).mp (hb X hX Y hYX)
      exact (hEdge (hpk x X hxX) (hpk y Y hyY)).mpr
        ((hp.2.2.2 x y X Y hxX hyY).mpr hYX)

/-- Every internal isomorphism of transitive sets extends over any prescribed
    larger transitive source set. This is a local extension, not a global automorphism. -/
theorem bafa_transitive_iso_extension (base : BaseCollection s) (hB : BAFACode s)
    {a b p A : U} (ha : TransitiveCode s a) (hb : TransitiveCode s b)
    (hp : MembershipIsoCode s a b p) (hA : TransitiveCode s A) (haA : Subset s a A) :
    ∃ C h, TransitiveCode s C ∧ Subset s b C ∧ MembershipIsoCode s A C h ∧
      ∀ x y, CodedRelation s p x y → CodedRelation s h x y := by
  obtain ⟨B, k, e, hk, hki, hkr, hpk, heG, heExt, hend, hEdge⟩ :=
    partial_iso_extension_graph base ha hb hp hA haA
  obtain ⟨C, f, hC, hf, hfi, hfr, hfix⟩ := hB b hb B e heG heExt hend
  obtain ⟨h, hh, hhr⟩ := coded_functions_compose base hk hf.1
    (fun x y hxy => (hkr y).mpr ⟨x, coded_function_domain hk hxy, hxy⟩)
  have hbi : Subset s b C := fun y hy => (hfr y).mpr ⟨y, hend.1 y hy, hfix y hy⟩
  refine ⟨C, h, hC, hbi, ⟨hh, ?_, ?_, ?_⟩, ?_⟩
  · intro x y z hxz hyz
    obtain ⟨X, hxX, hXz⟩ := (hhr x z).mp hxz
    obtain ⟨Y, hyY, hYz⟩ := (hhr y z).mp hyz
    have hXY := hfi X Y z hXz hYz
    exact hki x y X hxX (hXY.symm ▸ hyY)
  · intro z
    constructor
    · intro hz
      obtain ⟨X, hX, hXz⟩ := (hfr z).mp hz
      obtain ⟨x, hx, hxX⟩ := (hkr X).mp hX
      exact ⟨x, hx, (hhr x z).mpr ⟨X, hxX, hXz⟩⟩
    · rintro ⟨x, hx, hxz⟩
      obtain ⟨X, hxX, hXz⟩ := (hhr x z).mp hxz
      exact (hfr z).mpr ⟨X, (hkr X).mpr ⟨x, hx, hxX⟩, hXz⟩
  · intro x y z w hxz hyw
    obtain ⟨X, hxX, hXz⟩ := (hhr x z).mp hxz
    obtain ⟨Y, hyY, hYw⟩ := (hhr y w).mp hyw
    exact (hEdge x y X Y hxX hyY).symm.trans
      (decoration_injective_edge_reflection hf hfi
        ((hkr X).mpr ⟨x, coded_function_domain hk hxX, hxX⟩) hXz hYw).symm
  · intro x y hxy
    have hyb := (hp.2.2.1 y).mpr ⟨x, coded_function_domain hp.1 hxy, hxy⟩
    exact (hhr x y).mpr ⟨y, hpk x y hxy, hfix y hyb⟩

theorem bafa_transitive_iso_forth (base : BaseCollection s) (hB : BAFACode s)
    {a b p : U} (ha : TransitiveCode s a) (hb : TransitiveCode s b)
    (hp : MembershipIsoCode s a b p) (x : U) :
    ∃ A C h, TransitiveCode s A ∧ TransitiveCode s C ∧ Subset s a A ∧ Subset s b C ∧
      s x A ∧ MembershipIsoCode s A C h ∧
      ∀ u v, CodedRelation s p u v → CodedRelation s h u v := by
  obtain ⟨d, hd, hxd⟩ := transitive_sets_cover base x
  obtain ⟨A, hA, haA, hdA⟩ := transitive_sets_directed base ha hd
  obtain ⟨C, h, hC, hbC, hh, hph⟩ := bafa_transitive_iso_extension base hB ha hb hp hA haA
  exact ⟨A, C, h, hA, hC, haA, hbC, hdA x hxd, hh, hph⟩

theorem transitive_membership_iso_inverse (base : BaseCollection s) {a b p : U}
    (ha : TransitiveCode s a) (hb : TransitiveCode s b)
    (hp : MembershipIsoCode s a b p) :
    ∃ q, MembershipIsoCode s b a q ∧
      ∀ X x, CodedRelation s q X x ↔ CodedRelation s p x X := by
  obtain ⟨e, _, _, _, he, _⟩ := membership_graph_identity_decoration base ha
  obtain ⟨f, _, _, _, hf, _⟩ := membership_graph_identity_decoration base hb
  obtain ⟨q, hq, hqr⟩ := graph_iso_inverse base ((graph_iso_membership_iff he hf).mpr hp)
  exact ⟨q, (graph_iso_membership_iff hf he).mp hq, hqr⟩

theorem bafa_transitive_iso_back (base : BaseCollection s) (hB : BAFACode s)
    {a b p : U} (ha : TransitiveCode s a) (hb : TransitiveCode s b)
    (hp : MembershipIsoCode s a b p) (y : U) :
    ∃ A C h, TransitiveCode s A ∧ TransitiveCode s C ∧ Subset s a A ∧ Subset s b C ∧
      s y C ∧ MembershipIsoCode s A C h ∧
      ∀ u v, CodedRelation s p u v → CodedRelation s h u v := by
  obtain ⟨q, hq, hqr⟩ := transitive_membership_iso_inverse base ha hb hp
  obtain ⟨C, A, j, hC, hA, hbC, haA, hyC, hj, hqj⟩ :=
    bafa_transitive_iso_forth base hB hb ha hq y
  obtain ⟨h, hh, hhr⟩ := transitive_membership_iso_inverse base hC hA hj
  exact ⟨A, C, h, hA, hC, haA, hbC, hyC, hh,
    fun u v hpv => (hhr u v).mpr (hqj v u ((hqr v u).mpr hpv))⟩

#print axioms bafa_transitive_iso_extension
#print axioms bafa_transitive_iso_forth
end FullBridge
