import LeastGraphEquivariance
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

def QuotientMapCode (s : U → U → Prop) (a m b n p P : U) : Prop :=
  ∀ c C, CodedRelation s P c C ↔ ∃ x y, s x a ∧ CodedRelation s p x y ∧
    GraphClassCode s a m x c ∧ GraphClassCode s b n y C

def quotientMapFormula : Formula 7 :=
  .ex (.ex (.conj (.member 1 4) (.conj (relatedFormula 8 1 0)
    (.conj (graphClassFormula 3 1 4 5) (graphClassFormula 2 0 6 7)))))

theorem eval_quotientMapFormula (s : U → U → Prop) (C c a m b n p : U) :
    Eval s quotientMapFormula (cons C (cons c (cons a (cons m (cons b (cons n (cons p Fin.elim0))))))) ↔
      ∃ x y, s x a ∧ CodedRelation s p x y ∧ GraphClassCode s a m x c ∧
        GraphClassCode s b n y C := by
  simp only [quotientMapFormula, Eval, eval_relatedFormula, eval_graphClassFormula]
  rfl

theorem quotient_image_unique (base : BaseCollection s)
    {a e b f p m n x y X Y c C D : U}
    (hE : GraphCode s a e) (hF : GraphCode s b f)
    (hp : GraphIsoCode s a e b f p) (hm : LeastGraphRelationCode s a e m)
    (hn : LeastGraphRelationCode s b f n)
    (hxX : CodedRelation s p x X) (hyY : CodedRelation s p y Y)
    (hc : GraphClassCode s a m x c) (hd : GraphClassCode s a m y c)
    (hC : GraphClassCode s b n X C) (hD : GraphClassCode s b n Y D) : C = D := by
  have hxy := (least_graph_class_eq_iff base hE hm
    (coded_function_domain hp.1 hxX) (coded_function_domain hp.1 hyY) hc hd).mp rfl
  exact (least_graph_class_eq_iff base hF hn (graph_iso_value hp hxX) (graph_iso_value hp hyY) hC hD).mpr
    (least_relation_iso_forward base hF hp hm hn hxX hyY hxy)

theorem least_quotient_map_exists (base : BaseCollection s)
    {a e b f p m n A E B F : U}
    (hE : GraphCode s a e) (hF : GraphCode s b f)
    (hp : GraphIsoCode s a e b f p) (hm : LeastGraphRelationCode s a e m)
    (hn : LeastGraphRelationCode s b f n)
    (hA : ∀ c, s c A ↔ ∃ x, s x a ∧ GraphClassCode s a m x c)
    (hB : ∀ C, s C B ↔ ∃ y, s y b ∧ GraphClassCode s b n y C)
    (hQE : ∀ c d, CodedRelation s E c d ↔ GraphQuotientEdge s a m e c d)
    (hQF : ∀ C D, CodedRelation s F C D ↔ GraphQuotientEdge s b n f C D) :
    ∃ P, GraphIsoCode s A E B F P ∧ QuotientMapCode s a m b n p P := by
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union A B
  obtain ⟨P, hP⟩ := relation_comprehension_members base quotientMapFormula
    (cons a (cons m (cons b (cons n (cons p Fin.elim0))))) d
  have hi : QuotientMapCode s a m b n p P := by
    intro c C
    constructor
    · rintro ⟨z, hz, hpair⟩
      obtain ⟨c', C', _, _, hpair', hev⟩ := (hP z).mp hz
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpair hpair'
      exact (eval_quotientMapFormula s C c a m b n p).mp hev
    · rintro ⟨x, y, hx, hxy, hc, hC⟩
      obtain ⟨z, hz⟩ := orderedPair_exists base.pairing c C
      exact ⟨z, (hP z).mpr ⟨c, C,
        (hd c).mpr (Or.inl ((hA c).mpr ⟨x, hx, hc⟩)),
        (hd C).mpr (Or.inr ((hB C).mpr ⟨y, graph_iso_value hp hxy, hC⟩)), hz,
        (eval_quotientMapFormula s C c a m b n p).mpr ⟨x, y, hx, hxy, hc, hC⟩⟩, hz⟩
  have funP : FunctionCode s A P := by
    constructor
    · intro z hz
      obtain ⟨c, C, _, _, hpair, hev⟩ := (hP z).mp hz
      obtain ⟨x, y, hx, _, hc, _⟩ := (eval_quotientMapFormula s C c a m b n p).mp hev
      exact ⟨c, C, (hA c).mpr ⟨x, hx, hc⟩, hpair⟩
    · intro c hcA
      obtain ⟨x, hx, hc⟩ := (hA c).mp hcA
      obtain ⟨y, hxy, _⟩ := hp.1.2 x hx
      obtain ⟨C, hC⟩ := graph_class_exists base b n y
      refine ⟨C, (hi c C).mpr ⟨x, y, hx, hxy, hc, hC⟩, ?_⟩
      intro D hcD
      obtain ⟨x', y', _, hxy', hc', hD⟩ := (hi c D).mp hcD
      exact quotient_image_unique base hE hF hp hm hn hxy' hxy hc' hc hD hC
  refine ⟨P, ⟨funP, ?_, ?_, ?_⟩, hi⟩
  · intro c d C hcC hdC
    obtain ⟨x, X, hx, hxX, hc, hC⟩ := (hi c C).mp hcC
    obtain ⟨y, Y, hy, hyY, hd, hD⟩ := (hi d C).mp hdC
    have hXY := (least_graph_class_eq_iff base hF hn (graph_iso_value hp hxX) (graph_iso_value hp hyY) hC hD).mp rfl
    exact (least_graph_class_eq_iff base hE hm hx hy hc hd).mpr
      ((least_relation_iso_iff base hE hF hp hm hn hxX hyY).mpr hXY)
  · intro C
    constructor
    · intro hCB
      obtain ⟨y, hy, hC⟩ := (hB C).mp hCB
      obtain ⟨x, hx, hxy⟩ := (hp.2.2.1 y).mp hy
      obtain ⟨c, hc⟩ := graph_class_exists base a m x
      exact ⟨c, (hA c).mpr ⟨x, hx, hc⟩, (hi c C).mpr ⟨x, y, hx, hxy, hc, hC⟩⟩
    · rintro ⟨c, _, hcC⟩
      obtain ⟨x, y, _, hxy, _, hC⟩ := (hi c C).mp hcC
      exact (hB C).mpr ⟨y, graph_iso_value hp hxy, hC⟩
  · intro c d C D hcC hdD
    obtain ⟨x, X, _, hxX, hc, hC⟩ := (hi c C).mp hcC
    obtain ⟨y, Y, _, hyY, hd, hD⟩ := (hi d D).mp hdD
    exact (hQE c d).trans ((least_graph_iso_edge_iff base hE hF hp hm hn hxX hyY hc hd hC hD).trans
      (hQF C D).symm)

theorem quotient_map_identity (base : BaseCollection s) {a m p P : U}
    (hP : QuotientMapCode s a m a m p P)
    (hid : ∀ x y, CodedRelation s p x y → x = y) :
    ∀ c C, CodedRelation s P c C → c = C := by
  intro c C hcC
  obtain ⟨x, y, _, hxy, hc, hC⟩ := (hP c C).mp hcC
  have heq := hid x y hxy
  subst y
  exact graph_class_unique base hc hC

/-- Composition is preserved as an equality of actual coded relations. -/
theorem quotient_map_composition (base : BaseCollection s)
    {a e b f c p q r m n o B P Q R : U}
    (hp : GraphIsoCode s a e b f p) (hq : FunctionCode s b q)
    (hQfun : FunctionCode s B Q)
    (hP : QuotientMapCode s a m b n p P)
    (hQ : QuotientMapCode s b n c o q Q)
    (hR : QuotientMapCode s a m c o r R)
    (hcomp : ∀ x z, CodedRelation s r x z ↔ ∃ y, CodedRelation s p x y ∧ CodedRelation s q y z) :
    ∀ X Z, CodedRelation s R X Z ↔ ∃ Y, CodedRelation s P X Y ∧ CodedRelation s Q Y Z := by
  intro X Z
  constructor
  · intro hXZ
    obtain ⟨x, z, hx, hxz, hX, hZ⟩ := (hR X Z).mp hXZ
    obtain ⟨y, hxy, hyz⟩ := (hcomp x z).mp hxz
    obtain ⟨Y, hY⟩ := graph_class_exists base b n y
    exact ⟨Y, (hP X Y).mpr ⟨x, y, hx, hxy, hX, hY⟩,
      (hQ Y Z).mpr ⟨y, z, graph_iso_value hp hxy, hyz, hY, hZ⟩⟩
  · rintro ⟨Y, hXY, hYZ⟩
    obtain ⟨x, y, hx, hxy, hX, hY⟩ := (hP X Y).mp hXY
    obtain ⟨z, hyz, _⟩ := hq.2 y (graph_iso_value hp hxy)
    obtain ⟨Z', hZ'⟩ := graph_class_exists base c o z
    have hYZ' := (hQ Y Z').mpr ⟨y, z, graph_iso_value hp hxy, hyz, hY, hZ'⟩
    obtain ⟨W, _, hu⟩ := hQfun.2 Y (coded_function_domain hQfun hYZ)
    have hZZ := (hu Z' hYZ').trans (hu Z hYZ).symm
    exact (hR X Z).mpr ⟨x, z, hx, (hcomp x z).mpr ⟨y, hxy, hyz⟩, hX, hZZ ▸ hZ'⟩



theorem quotient_map_unique (base : BaseCollection s) {a m b n p A P Q : U}
    (hPf : FunctionCode s A P) (hQf : FunctionCode s A Q)
    (hP : QuotientMapCode s a m b n p P) (hQ : QuotientMapCode s a m b n p Q) : P = Q := by
  apply function_code_extensional base.extensional hPf hQf
  intro c C D hcC hcD
  have hcC' := (hQ c C).mpr ((hP c C).mp hcC)
  obtain ⟨W, _, hu⟩ := hQf.2 c (coded_function_domain hQf hcD)
  exact (hu C hcC').trans (hu D hcD).symm

/-- A given externally indexed family of internal automorphisms descends coherently.
    This does not construct such a family or a symmetric model. -/
theorem quotient_map_family_lift (base : BaseCollection s)
    {I : Type v} (one : I) (mul : I → I → I) (act : I → U)
    {a e m A E : U} (hG : GraphCode s a e) (hm : LeastGraphRelationCode s a e m)
    (hA : ∀ c, s c A ↔ ∃ x, s x a ∧ GraphClassCode s a m x c)
    (hQE : ∀ c d, CodedRelation s E c d ↔ GraphQuotientEdge s a m e c d)
    (hAct : ∀ i, GraphIsoCode s a e a e (act i))
    (hOne : ∀ x y, CodedRelation s (act one) x y → x = y)
    (hMul : ∀ i j x z, CodedRelation s (act (mul i j)) x z ↔
      ∃ y, CodedRelation s (act j) x y ∧ CodedRelation s (act i) y z) :
    ∃ out : I → U,
      (∀ i, GraphIsoCode s A E A E (out i) ∧ QuotientMapCode s a m a m (act i) (out i)) ∧
      (∀ X Y, CodedRelation s (out one) X Y → X = Y) ∧
      (∀ i j X Z, CodedRelation s (out (mul i j)) X Z ↔
        ∃ Y, CodedRelation s (out j) X Y ∧ CodedRelation s (out i) Y Z) := by
  classical
  have existsMap : ∀ i, ∃ P, GraphIsoCode s A E A E P ∧ QuotientMapCode s a m a m (act i) P :=
    fun i => least_quotient_map_exists base hG hG (hAct i) hm hm hA hA hQE hQE
  let out : I → U := fun i => Classical.choose (existsMap i)
  have hout : ∀ i, GraphIsoCode s A E A E (out i) ∧ QuotientMapCode s a m a m (act i) (out i) :=
    fun i => Classical.choose_spec (existsMap i)
  refine ⟨out, hout, quotient_map_identity base (hout one).2 hOne, ?_⟩
  intro i j
  exact quotient_map_composition base (hAct j) (hAct i).1 (hout i).1.1
    (hout j).2 (hout i).2 (hout (mul i j)).2 (hMul i j)

#print axioms least_quotient_map_exists
#print axioms quotient_map_composition
#print axioms quotient_map_family_lift
end FullBridge
