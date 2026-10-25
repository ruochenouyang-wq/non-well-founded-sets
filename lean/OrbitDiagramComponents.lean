import OrbitDiagramCodes
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

structure OrbitDiagramComponent (s : U → U → Prop) (N E p a r : U) where
  domain : U
  code : U
  function : FunctionCode s a code
  injective : InjectiveCode s code
  range : RangeCode s a code domain
  values : ∀ x X, CodedRelation s code x X ↔ s x a ∧ IsOrderedPair s X p x
  closed : GraphClosedCode s N E domain
  transported : ∀ x y X Y, CodedRelation s code x X → CodedRelation s code y Y →
    (CodedRelation s E X Y ↔ CodedRelation s r x y)
  extensional : GraphExtensionalCode s domain E

theorem orbit_diagram_component_exists (base : BaseCollection s) {O N E p t a r : U}
    (hN : ∀ X, s X N ↔ OrbitDiagramNode s O X)
    (hE : ∀ X Y, CodedRelation s E X Y ↔ OrbitDiagramEdge s O X Y)
    (hpO : s p O) (hpar : OrbitGraphParameters s p t a r) (hReq : BafaRequestCode s p) :
    Nonempty (OrbitDiagramComponent s N E p a r) := by
  obtain ⟨_, hG, hExt, _⟩ := bafa_request_parameters hReq hpar
  obtain ⟨k, hk, hkr⟩ := definable_function_code base (orderedPairFormula (n := 3) 0 2 1)
    (cons p Fin.elim0) a (by
      intro x _
      obtain ⟨X, hX⟩ := orderedPair_exists base.pairing p x
      exact ⟨X, (eval_orderedPairFormula s 0 2 1 _).mpr hX,
        fun Y hY => orderedPair_unique base.extensional ((eval_orderedPairFormula s 0 2 1 _).mp hY) hX⟩)
  have hv : ∀ x X, CodedRelation s k x X ↔ s x a ∧ IsOrderedPair s X p x := by
    intro x X
    exact (hkr x X).trans (and_congr Iff.rfl (eval_orderedPairFormula s 0 2 1 _))
  have hki : InjectiveCode s k := by
    intro x y Z hx hy
    exact (orderedPair_injective ((hv x Z).mp hx).2 ((hv y Z).mp hy).2).2
  obtain ⟨c, hc⟩ := coded_image_set_exists base k a
  have hct : Subset s c N := by
    intro X hX
    obtain ⟨x, hx, hxX⟩ := (hc X).mp hX
    exact (hN X).mpr ⟨p, t, a, r, x, hpO, hpar, hx, ((hv x X).mp hxX).2⟩
  have hclosed : GraphClosedCode s N E c := by
    refine ⟨hct, ?_⟩
    intro X hX Y hXY
    obtain ⟨x, hx, hxX⟩ := (hc X).mp hX
    obtain ⟨q, t', a', r', u, v, _, hpar', hXu, hYv, huv⟩ := (hE X Y).mp hXY
    obtain ⟨hqp, hux⟩ := orderedPair_injective hXu ((hv x X).mp hxX).2
    subst q
    subst u
    obtain ⟨ht, ha, hr⟩ := orbit_graph_parameters_unique hpar' hpar
    subst t'
    subst a'
    subst r'
    have hva := (graphCode_endpoints hG huv).2
    exact (hc Y).mpr ⟨v, hva, (hv v Y).mpr ⟨hva, hYv⟩⟩
  have htransport : ∀ x y X Y, CodedRelation s k x X → CodedRelation s k y Y →
      (CodedRelation s E X Y ↔ CodedRelation s r x y) := by
    intro x y X Y hxX hyY
    constructor
    · intro hXY
      obtain ⟨q, t', a', r', u, v, _, hpar', hXu, hYv, huv⟩ := (hE X Y).mp hXY
      obtain ⟨hqp, hux⟩ := orderedPair_injective hXu ((hv x X).mp hxX).2
      have hvy := (orderedPair_injective hYv ((hv y Y).mp hyY).2).2
      subst q
      subst u
      subst v
      have hrr := (orbit_graph_parameters_unique hpar' hpar).2.2
      exact hrr ▸ huv
    · intro hxy
      exact (hE X Y).mpr ⟨p, t, a, r, x, y, hpO, hpar,
        ((hv x X).mp hxX).2, ((hv y Y).mp hyY).2, hxy⟩
  have hext : GraphExtensionalCode s c E := by
    intro X hX Y hY hrows
    obtain ⟨x, hx, hxX⟩ := (hc X).mp hX
    obtain ⟨y, hy, hyY⟩ := (hc Y).mp hY
    have hxy : x = y := by
      apply hExt x hx y hy
      intro z hz
      obtain ⟨Z, hzZ, _⟩ := hk.2 z hz
      exact (htransport x z X Z hxX hzZ).symm.trans
        ((hrows Z ((hc Z).mpr ⟨z, hz, hzZ⟩)).trans (htransport y z Y Z hyY hzZ))
    subst y
    exact coded_function_value_unique hk hxX hyY
  exact ⟨⟨c, k, hk, hki, hc, hv, hclosed, htransport, hext⟩⟩

theorem orbit_graph_parameter_code_unique (base : BaseCollection s) {p q t a r : U}
    (hp : OrbitGraphParameters s p t a r) (hq : OrbitGraphParameters s q t a r) : p = q := by
  obtain ⟨b, hb, hp⟩ := hp
  obtain ⟨c, hc, hq⟩ := hq
  have hbc := orderedPair_unique base.extensional hb hc
  exact orderedPair_unique base.extensional hp (hbc.symm ▸ hq)

theorem graph_parameter_stabilizer_iff (base : BaseCollection s) {j : U → U}
    (hj : ElementaryMap s s j) {p t a r : U} (hp : OrbitGraphParameters s p t a r) :
    j p = p ↔ j t = t ∧ j a = a ∧ j r = r := by
  constructor
  · intro h
    have hh := elementary_map_graph_parameters hj hp
    rw [h] at hh
    exact orbit_graph_parameters_unique hh hp
  · rintro ⟨ht, ha, hr⟩
    have hh := elementary_map_graph_parameters hj hp
    rw [ht, ha, hr] at hh
    exact orbit_graph_parameter_code_unique base hh hp

theorem parameter_stabilizer_preserves_component (base : BaseCollection s) {j : U → U}
    (hj : ElementaryMap s s j) {N E p t a r : U}
    (C : OrbitDiagramComponent s N E p a r) (hp : OrbitGraphParameters s p t a r)
    (hfix : j p = p) : ∀ X, s X C.domain → s (j X) C.domain := by
  have ha := ((graph_parameter_stabilizer_iff base hj hp).mp hfix).2.1
  intro X hX
  obtain ⟨x, hx, hxX⟩ := (C.range X).mp hX
  have hjx : s (j x) a := by
    have h := (hj (Formula.member (n := 2) 0 1) (cons x (cons a Fin.elim0))).mp hx
    change s (j x) (j a) at h
    rwa [ha] at h
  have hpair := elementary_map_ordered_pair hj ((C.values x X).mp hxX).2
  rw [hfix] at hpair
  exact (C.range (j X)).mpr ⟨j x, hjx, (C.values (j x) (j X)).mpr ⟨hjx, hpair⟩⟩

#print axioms orbit_diagram_component_exists
#print axioms graph_parameter_stabilizer_iff
end FullBridge
