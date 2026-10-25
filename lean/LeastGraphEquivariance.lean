import ClosedGraphPreservation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- An internal bijection preserving and reflecting graph edges. -/
def GraphIsoCode (s : U → U → Prop) (a e b f p : U) : Prop :=
  FunctionCode s a p ∧ InjectiveCode s p ∧ RangeCode s a p b ∧
    ∀ x y X Y, CodedRelation s p x X → CodedRelation s p y Y →
      (CodedRelation s e x y ↔ CodedRelation s f X Y)

theorem graph_iso_value {a e b f p x X : U} (hp : GraphIsoCode s a e b f p)
    (hxX : CodedRelation s p x X) : s X b :=
  (hp.2.2.1 X).mpr ⟨x, coded_function_domain hp.1 hxX, hxX⟩

theorem graph_iso_inverse (base : BaseCollection s) {a e b f p : U}
    (hp : GraphIsoCode s a e b f p) :
    ∃ q, GraphIsoCode s b f a e q ∧
      ∀ X x, CodedRelation s q X x ↔ CodedRelation s p x X := by
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union a b
  obtain ⟨q, hq⟩ := relation_comprehension_members base
    (relatedFormula (n := 3) 2 0 1) (cons p Fin.elim0) d
  have hi : ∀ X x, CodedRelation s q X x ↔ CodedRelation s p x X := by
    intro X x
    constructor
    · rintro ⟨z, hz, hpair⟩
      obtain ⟨X', x', _, _, hpair', hev⟩ := (hq z).mp hz
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpair hpair'
      exact (eval_relatedFormula s 2 0 1 _).mp hev
    · intro hxX
      obtain ⟨z, hz⟩ := orderedPair_exists base.pairing X x
      exact ⟨z, (hq z).mpr ⟨X, x, (hd X).mpr (Or.inr (graph_iso_value hp hxX)),
        (hd x).mpr (Or.inl (coded_function_domain hp.1 hxX)), hz,
        (eval_relatedFormula s 2 0 1 _).mpr hxX⟩, hz⟩
  refine ⟨q, ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, hi⟩
  · intro z hz
    obtain ⟨X, x, _, _, hpair, hev⟩ := (hq z).mp hz
    exact ⟨X, x, graph_iso_value hp ((eval_relatedFormula s 2 0 1 _).mp hev), hpair⟩
  · intro X hX
    obtain ⟨x, _, hxX⟩ := (hp.2.2.1 X).mp hX
    exact ⟨x, (hi X x).mpr hxX, fun y hy => hp.2.1 y x X ((hi X y).mp hy) hxX⟩
  · intro X Y x hXx hYx
    have hxX := (hi X x).mp hXx
    have hxY := (hi Y x).mp hYx
    obtain ⟨v, _, hu⟩ := hp.1.2 x (coded_function_domain hp.1 hxX)
    exact (hu X hxX).trans (hu Y hxY).symm
  · intro x
    constructor
    · intro hx
      obtain ⟨X, hxX, _⟩ := hp.1.2 x hx
      exact ⟨X, graph_iso_value hp hxX, (hi X x).mpr hxX⟩
    · rintro ⟨X, _, hXx⟩
      exact coded_function_domain hp.1 ((hi X x).mp hXx)
  · intro X Y x y hXx hYy
    exact (hp.2.2.2 x y X Y ((hi X x).mp hXx) ((hi Y y).mp hYy)).symm

def isoPullbackFormula : Formula 4 :=
  .ex (.ex (.conj (relatedFormula 4 3 1)
    (.conj (relatedFormula 4 2 0) (relatedFormula 5 1 0))))

theorem eval_isoPullbackFormula (s : U → U → Prop) (y x p n : U) :
    Eval s isoPullbackFormula (cons y (cons x (cons p (cons n Fin.elim0)))) ↔
      ∃ X Y, CodedRelation s p x X ∧ CodedRelation s p y Y ∧ CodedRelation s n X Y := by
  simp only [isoPullbackFormula, Eval, eval_relatedFormula]
  rfl

theorem least_relation_iso_forward (base : BaseCollection s)
    {a e b f p m n : U} (hF : GraphCode s b f)
    (hp : GraphIsoCode s a e b f p) (hm : LeastGraphRelationCode s a e m)
    (hn : LeastGraphRelationCode s b f n) {x y X Y : U}
    (hxX : CodedRelation s p x X) (hyY : CodedRelation s p y Y)
    (hxy : CodedRelation s m x y) : CodedRelation s n X Y := by
  obtain ⟨k, hkG, hk⟩ := normalized_relation_comprehension base isoPullbackFormula
    (cons p (cons n Fin.elim0)) a
  have hi : ∀ u v, CodedRelation s k u v ↔ s u a ∧ s v a ∧
      ∃ U' V', CodedRelation s p u U' ∧ CodedRelation s p v V' ∧ CodedRelation s n U' V' := by
    intro u v
    exact (hk u v).trans (and_congr_right (fun _ => and_congr_right
      (fun _ => eval_isoPullbackFormula s v u p n)))
  have same : ∀ u U' V', CodedRelation s p u U' → CodedRelation s p u V' → U' = V' := by
    intro u U' V' huU huV
    obtain ⟨w, _, hu⟩ := hp.1.2 u (coded_function_domain hp.1 huU)
    exact (hu U' huU).trans (hu V' huV).symm
  have hpre : GraphPreFixedCode s a e k := by
    refine ⟨hkG, ?_, ?_⟩
    · intro u hu
      obtain ⟨U', huU, _⟩ := hp.1.2 u hu
      exact (hi u u).mpr ⟨hu, hu, U', U', huU, huU, hn.1.2.1 U' (graph_iso_value hp huU)⟩
    · intro u v hu hv hmatch
      obtain ⟨U', huU, _⟩ := hp.1.2 u hu
      obtain ⟨V', hvV, _⟩ := hp.1.2 v hv
      refine (hi u v).mpr ⟨hu, hv, U', V', huU, hvV, ?_⟩
      apply hn.1.2.2 U' V' (graph_iso_value hp huU) (graph_iso_value hp hvV)
      constructor
      · intro Z hUZ
        obtain ⟨z, _, hzZ⟩ := (hp.2.2.1 Z).mp (graphCode_endpoints hF hUZ).2
        obtain ⟨w, hvw, hzw⟩ := hmatch.1 z ((hp.2.2.2 u z U' Z huU hzZ).mpr hUZ)
        obtain ⟨_, _, Z', W, hzZ', hwW, hnZW⟩ := (hi z w).mp hzw
        have hz := same z Z' Z hzZ' hzZ
        exact ⟨W, (hp.2.2.2 v w V' W hvV hwW).mp hvw, hz ▸ hnZW⟩
      · intro W hVW
        obtain ⟨w, _, hwW⟩ := (hp.2.2.1 W).mp (graphCode_endpoints hF hVW).2
        obtain ⟨z, huz, hzw⟩ := hmatch.2 w ((hp.2.2.2 v w V' W hvV hwW).mpr hVW)
        obtain ⟨_, _, Z, W', hzZ, hwW', hnZW⟩ := (hi z w).mp hzw
        have hw := same w W' W hwW' hwW
        exact ⟨Z, (hp.2.2.2 u z U' Z huU hzZ).mp huz, hw ▸ hnZW⟩
  obtain ⟨_, _, X', Y', hxX', hyY', hnXY⟩ := (hi x y).mp (hm.2 k hpre x y hxy)
  have hX := same x X' X hxX' hxX
  have hY := same y Y' Y hyY' hyY
  exact hX ▸ hY ▸ hnXY

theorem least_relation_iso_iff (base : BaseCollection s)
    {a e b f p m n : U} (hE : GraphCode s a e) (hF : GraphCode s b f)
    (hp : GraphIsoCode s a e b f p) (hm : LeastGraphRelationCode s a e m)
    (hn : LeastGraphRelationCode s b f n) {x y X Y : U}
    (hxX : CodedRelation s p x X) (hyY : CodedRelation s p y Y) :
    CodedRelation s m x y ↔ CodedRelation s n X Y := by
  constructor
  · exact least_relation_iso_forward base hF hp hm hn hxX hyY
  · intro hXY
    obtain ⟨q, hq, hqi⟩ := graph_iso_inverse base hp
    exact least_relation_iso_forward base hE hq hn hm ((hqi X x).mpr hxX) ((hqi Y y).mpr hyY) hXY



theorem least_graph_iso_edge_forward (base : BaseCollection s)
    {a e b f p m n x y X Y c d C D : U}
    (hE : GraphCode s a e) (hF : GraphCode s b f)
    (hp : GraphIsoCode s a e b f p) (hm : LeastGraphRelationCode s a e m)
    (hn : LeastGraphRelationCode s b f n)
    (hxX : CodedRelation s p x X) (hyY : CodedRelation s p y Y)
    (hc : GraphClassCode s a m x c) (hd : GraphClassCode s a m y d)
    (hC : GraphClassCode s b n X C) (hD : GraphClassCode s b n Y D)
    (hcd : GraphQuotientEdge s a m e c d) : GraphQuotientEdge s b n f C D := by
  have hx := coded_function_domain hp.1 hxX
  have hy := coded_function_domain hp.1 hyY
  obtain ⟨z, hz, hxz, hzd⟩ :=
    (least_graph_quotient_edge_from_representative base hE hm hx hc).mp hcd
  obtain ⟨Z, hzZ, _⟩ := hp.1.2 z hz
  have hzy := (least_graph_class_eq_iff base hE hm hz hy hzd hd).mp rfl
  have hZY := least_relation_iso_forward base hF hp hm hn hzZ hyY hzy
  obtain ⟨K, hK⟩ := graph_class_exists base b n Z
  have hKD := (least_graph_class_eq_iff base hF hn (graph_iso_value hp hzZ)
    (graph_iso_value hp hyY) hK hD).mpr hZY
  exact ⟨X, Z, graph_iso_value hp hxX, graph_iso_value hp hzZ,
    hC, hKD ▸ hK, (hp.2.2.2 x z X Z hxX hzZ).mp hxz⟩

theorem least_graph_iso_edge_iff (base : BaseCollection s)
    {a e b f p m n x y X Y c d C D : U}
    (hE : GraphCode s a e) (hF : GraphCode s b f)
    (hp : GraphIsoCode s a e b f p) (hm : LeastGraphRelationCode s a e m)
    (hn : LeastGraphRelationCode s b f n)
    (hxX : CodedRelation s p x X) (hyY : CodedRelation s p y Y)
    (hc : GraphClassCode s a m x c) (hd : GraphClassCode s a m y d)
    (hC : GraphClassCode s b n X C) (hD : GraphClassCode s b n Y D) :
    GraphQuotientEdge s a m e c d ↔ GraphQuotientEdge s b n f C D := by
  constructor
  · exact least_graph_iso_edge_forward base hE hF hp hm hn hxX hyY hc hd hC hD
  · intro hCD
    obtain ⟨q, hq, hqi⟩ := graph_iso_inverse base hp
    exact least_graph_iso_edge_forward base hF hE hq hn hm
      ((hqi X x).mpr hxX) ((hqi Y y).mpr hyY) hC hD hc hd hCD

#print axioms least_relation_iso_iff
#print axioms least_graph_iso_edge_iff
end FullBridge
