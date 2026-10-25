import LeastQuotientMaps
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- An actual internal bijection between induced membership structures. -/
def MembershipIsoCode (s : U → U → Prop) (a b p : U) : Prop :=
  FunctionCode s a p ∧ InjectiveCode s p ∧ RangeCode s a p b ∧
    ∀ x y X Y, CodedRelation s p x X → CodedRelation s p y Y →
      (s y x ↔ s Y X)

theorem membership_iso_bisimulation {a b p : U}
    (ha : TransitiveCode s a) (hb : TransitiveCode s b)
    (hp : MembershipIsoCode s a b p) : Bisimulation s (CodedRelation s p) := by
  intro x X hxX
  have hx := coded_function_domain hp.1 hxX
  have hX := (hp.2.2.1 X).mpr ⟨x, hx, hxX⟩
  constructor
  · intro y hy
    obtain ⟨Y, hyY, _⟩ := hp.1.2 y (ha x hx y hy)
    exact ⟨Y, (hp.2.2.2 x y X Y hxX hyY).mp hy, hyY⟩
  · intro Y hY
    obtain ⟨y, _, hyY⟩ := (hp.2.2.1 Y).mp (hb X hX Y hY)
    exact ⟨y, (hp.2.2.2 x y X Y hxX hyY).mpr hY, hyY⟩

theorem membership_iso_over_quotient (base : BaseCollection s) {a b p : U}
    (ha : TransitiveCode s a) (hb : TransitiveCode s b)
    (hp : MembershipIsoCode s a b p) : OverQuotientCode base a b p := by
  refine ⟨hp.1, ?_⟩
  intro x y hxy
  exact ⟨(hp.2.2.1 y).mpr ⟨x, coded_function_domain hp.1 hxy, hxy⟩,
    (internal_code_eq base x y).mpr
      (coded_bisimulation_internalBehavior (membership_iso_bisimulation ha hb hp) hxy)⟩

theorem membership_iso_root_code (base : BaseCollection s) {a b p : U}
    (ha : TransitiveCode s a) (hb : TransitiveCode s b)
    (hp : MembershipIsoCode s a b p) : internalCode base a = internalCode base b := by
  have hq := membership_iso_over_quotient base ha hb hp
  apply internal_extensional base
  intro Z
  constructor
  · intro hZ
    obtain ⟨x, hx, rfl⟩ := (internal_exact_members base a Z).mp hZ
    obtain ⟨y, hxy, _⟩ := hp.1.2 x hx
    exact (internal_exact_members base b (internalCode base x)).mpr
      ⟨y, (hq.2 x y hxy).1, (hq.2 x y hxy).2.symm⟩
  · intro hZ
    obtain ⟨y, hy, rfl⟩ := (internal_exact_members base b Z).mp hZ
    obtain ⟨x, hx, hxy⟩ := (hp.2.2.1 y).mp hy
    exact (internal_exact_members base a (internalCode base y)).mpr
      ⟨x, hx, (hq.2 x y hxy).2⟩

theorem membership_automorphism_rigid (base : BaseCollection s) {a p : U}
    (ha : TransitiveCode s a) (hi : ParameterInjective base a)
    (hp : MembershipIsoCode s a a p) :
    ∀ x y, CodedRelation s p x y → x = y := by
  intro x y hxy
  have h := (membership_iso_over_quotient base ha ha hp).2 x y hxy
  exact hi x y (coded_function_domain hp.1 hxy) h.1 h.2

theorem membership_iso_unique (base : BaseCollection s) {a b p q : U}
    (ha : TransitiveCode s a) (hb : TransitiveCode s b)
    (hi : ParameterInjective base b)
    (hp : MembershipIsoCode s a b p) (hq : MembershipIsoCode s a b q) : p = q :=
  lift_comparison_unique base hi (membership_iso_over_quotient base ha hb hp)
    (membership_iso_over_quotient base ha hb hq)

theorem membership_iso_iff_same_code (base : BaseCollection s) {a b : U}
    (ha : TransitiveCode s a) (hb : TransitiveCode s b)
    (hia : ParameterInjective base a) (hib : ParameterInjective base b) :
    (∃ p, MembershipIsoCode s a b p) ↔ internalCode base a = internalCode base b := by
  constructor
  · rintro ⟨p, hp⟩
    exact membership_iso_root_code base ha hb hp
  · intro hab
    obtain ⟨p, hp, hpr⟩ := lift_comparison_exists base hib hab
    refine ⟨p, hp.1, lift_comparison_injective base hia hp, hpr, ?_⟩
    intro x y X Y hxX hyY
    exact lift_comparison_members base ha hb hia hib hp
      (coded_function_domain hp.1 hyY) (coded_function_domain hp.1 hxX) hyY hxX

theorem graph_iso_membership_iff {a e b f p : U}
    (he : ∀ x y, CodedRelation s e x y ↔ s x a ∧ s y x)
    (hf : ∀ X Y, CodedRelation s f X Y ↔ s X b ∧ s Y X) :
    GraphIsoCode s a e b f p ↔ MembershipIsoCode s a b p := by
  constructor
  · intro hp
    refine ⟨hp.1, hp.2.1, hp.2.2.1, ?_⟩
    intro x y X Y hxX hyY
    have hx := coded_function_domain hp.1 hxX
    have hX := graph_iso_value hp hxX
    exact ⟨fun h => ((hf X Y).mp ((hp.2.2.2 x y X Y hxX hyY).mp
      ((he x y).mpr ⟨hx, h⟩))).2,
      fun h => ((he x y).mp ((hp.2.2.2 x y X Y hxX hyY).mpr
      ((hf X Y).mpr ⟨hX, h⟩))).2⟩
  · intro hp
    refine ⟨hp.1, hp.2.1, hp.2.2.1, ?_⟩
    intro x y X Y hxX hyY
    have hx := coded_function_domain hp.1 hxX
    have hX := (hp.2.2.1 X).mpr ⟨x, hx, hxX⟩
    exact ⟨fun h => (hf X Y).mpr ⟨hX, (hp.2.2.2 x y X Y hxX hyY).mp ((he x y).mp h).2⟩,
      fun h => (he x y).mpr ⟨hx, (hp.2.2.2 x y X Y hxX hyY).mpr ((hf X Y).mp h).2⟩⟩

/-- Composition is constructed as a normalized internal function, including its members. -/
theorem graph_iso_composition (base : BaseCollection s) {a e b f c g p q : U}
    (hp : GraphIsoCode s a e b f p) (hq : GraphIsoCode s b f c g q) :
    ∃ r, GraphIsoCode s a e c g r ∧
      ∀ x z, CodedRelation s r x z ↔
        ∃ y, CodedRelation s p x y ∧ CodedRelation s q y z := by
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union a c
  obtain ⟨r, hr⟩ := relation_comprehension_members base compositionFormula
    (cons p (cons q Fin.elim0)) d
  have hi : ∀ x z, CodedRelation s r x z ↔ ∃ y, CodedRelation s p x y ∧ CodedRelation s q y z := by
    intro x z
    constructor
    · rintro ⟨v, hv, hvxz⟩
      obtain ⟨x', z', _, _, hv', hev⟩ := (hr v).mp hv
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hvxz hv'
      exact (eval_compositionFormula x z p q).mp hev
    · rintro ⟨y, hxy, hyz⟩
      obtain ⟨v, hv⟩ := orderedPair_exists base.pairing x z
      exact ⟨v, (hr v).mpr ⟨x, z, (hd x).mpr (Or.inl (coded_function_domain hp.1 hxy)),
        (hd z).mpr (Or.inr (graph_iso_value hq hyz)), hv,
        (eval_compositionFormula x z p q).mpr ⟨y, hxy, hyz⟩⟩, hv⟩
  refine ⟨r, ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, hi⟩
  · intro v hv
    obtain ⟨x, z, _, _, hpair, hev⟩ := (hr v).mp hv
    obtain ⟨y, hxy, _⟩ := (eval_compositionFormula x z p q).mp hev
    exact ⟨x, z, coded_function_domain hp.1 hxy, hpair⟩
  · intro x hx
    obtain ⟨y, hxy, huy⟩ := hp.1.2 x hx
    obtain ⟨z, hyz, huz⟩ := hq.1.2 y (graph_iso_value hp hxy)
    refine ⟨z, (hi x z).mpr ⟨y, hxy, hyz⟩, ?_⟩
    intro Z hxZ
    obtain ⟨Y, hxY, hYZ⟩ := (hi x Z).mp hxZ
    have heq := huy Y hxY
    subst Y
    exact huz Z hYZ
  · intro x X z hxz hXz
    obtain ⟨y, hxy, hyz⟩ := (hi x z).mp hxz
    obtain ⟨Y, hXY, hYz⟩ := (hi X z).mp hXz
    have heq := hq.2.1 y Y z hyz hYz
    subst Y
    exact hp.2.1 x X y hxy hXY
  · intro z
    constructor
    · intro hz
      obtain ⟨y, hy, hyz⟩ := (hq.2.2.1 z).mp hz
      obtain ⟨x, hx, hxy⟩ := (hp.2.2.1 y).mp hy
      exact ⟨x, hx, (hi x z).mpr ⟨y, hxy, hyz⟩⟩
    · rintro ⟨x, _, hxz⟩
      obtain ⟨y, _, hyz⟩ := (hi x z).mp hxz
      exact graph_iso_value hq hyz
  · intro x y X Y hxX hyY
    obtain ⟨v, hxv, hvX⟩ := (hi x X).mp hxX
    obtain ⟨w, hyw, hwY⟩ := (hi y Y).mp hyY
    exact (hp.2.2.2 x y v w hxv hyw).trans (hq.2.2.2 v w X Y hvX hwY)

theorem injective_decoration_graph_iso (base : BaseCollection s) {a e f : U}
    (hf : DecorationCode s a e f) (hi : InjectiveCode s f) :
    ∃ T E, TransitiveCode s T ∧ GraphCode s T E ∧
      (∀ X Y, CodedRelation s E X Y ↔ s X T ∧ s Y X) ∧
      GraphIsoCode s a e T E f := by
  obtain ⟨T, ht, hr⟩ := decoration_transitive_range base hf
  obtain ⟨E, _, hE, _, hEr, _⟩ := membership_graph_identity_decoration base ht
  refine ⟨T, E, ht, hE, hEr, hf.1, hi, hr, ?_⟩
  intro x y X Y hxX hyY
  have hx := coded_function_domain hf.1 hxX
  have hX := (hr X).mpr ⟨x, hx, hxX⟩
  exact (decoration_injective_edge_reflection hf hi hx hxX hyY).symm.trans
    ⟨fun h => (hEr X Y).mpr ⟨hX, h⟩, fun h => ((hEr X Y).mp h).2⟩

theorem graph_automorphism_transport (base : BaseCollection s) {a e T E f p : U}
    (hf : GraphIsoCode s a e T E f) (hp : GraphIsoCode s a e a e p) :
    ∃ P, GraphIsoCode s T E T E P ∧
      ∀ X Y, CodedRelation s P X Y ↔
        ∃ x y, CodedRelation s f x X ∧ CodedRelation s p x y ∧ CodedRelation s f y Y := by
  obtain ⟨g, hg, hgr⟩ := graph_iso_inverse base hf
  obtain ⟨h, hh, hhr⟩ := graph_iso_composition base hg hp
  obtain ⟨P, hP, hPr⟩ := graph_iso_composition base hh hf
  refine ⟨P, hP, ?_⟩
  intro X Y
  constructor
  · intro hXY
    obtain ⟨y, hXy, hyY⟩ := (hPr X Y).mp hXY
    obtain ⟨x, hXx, hxy⟩ := (hhr X y).mp hXy
    exact ⟨x, y, (hgr X x).mp hXx, hxy, hyY⟩
  · rintro ⟨x, y, hxX, hxy, hyY⟩
    exact (hPr X Y).mpr ⟨y, (hhr X y).mpr ⟨x, (hgr X x).mpr hxX, hxy⟩, hyY⟩

theorem bafa_realizes_invisible_symmetries (base : BaseCollection s)
    (hB : BAFACode s) {a e : U} (hG : GraphCode s a e)
    (hE : GraphExtensionalCode s a e) :
    ∃ T f, TransitiveCode s T ∧ DecorationCode s a e f ∧
      InjectiveCode s f ∧ RangeCode s a f T ∧
      ∀ p, GraphIsoCode s a e a e p →
        ∃ P, MembershipIsoCode s T T P ∧
          (∀ X Y, CodedRelation s P X Y ↔
            ∃ x y, CodedRelation s f x X ∧ CodedRelation s p x y ∧ CodedRelation s f y Y) ∧
          (∀ X Y, CodedRelation s P X Y → internalCode base X = internalCode base Y) ∧
          (∀ x y X Y, CodedRelation s p x y → CodedRelation s f x X →
            CodedRelation s f y Y → x ≠ y → X ≠ Y) := by
  obtain ⟨f, hf, hfi⟩ := bafa_extensional_realization base.empty hB a e hG hE
  obtain ⟨T, E, ht, _, hEr, hfg⟩ := injective_decoration_graph_iso base hf hfi
  refine ⟨T, f, ht, hf, hfi, hfg.2.2.1, ?_⟩
  intro p hp
  obtain ⟨P, hP, hPr⟩ := graph_automorphism_transport base hfg hp
  have hPM := (graph_iso_membership_iff hEr hEr).mp hP
  refine ⟨P, hPM, hPr, ?_, ?_⟩
  · intro X Y hXY
    exact ((membership_iso_over_quotient base ht ht hPM).2 X Y hXY).2
  · intro x y X Y _ hxX hyY hne heq
    subst Y
    exact hne (hfi x y X hxX hyY)

#print axioms bafa_realizes_invisible_symmetries
#print axioms membership_iso_iff_same_code
end FullBridge
