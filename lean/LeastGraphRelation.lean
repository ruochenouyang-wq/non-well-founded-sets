import FixedSolvability
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def RowMatching (s : U → U → Prop) (e r x y : U) : Prop :=
  (∀ u, CodedRelation s e x u → ∃ v, CodedRelation s e y v ∧ CodedRelation s r u v) ∧
  (∀ v, CodedRelation s e y v → ∃ u, CodedRelation s e x u ∧ CodedRelation s r u v)

def rowMatchingFormula {n} (e r x y : Fin n) : Formula n :=
  .conj
    (.all (.impl (relatedFormula e.succ x.succ 0)
      (.ex (.conj (relatedFormula e.succ.succ y.succ.succ 0)
        (relatedFormula r.succ.succ 1 0)))))
    (.all (.impl (relatedFormula e.succ y.succ 0)
      (.ex (.conj (relatedFormula e.succ.succ x.succ.succ 0)
        (relatedFormula r.succ.succ 0 1)))))

theorem eval_rowMatchingFormula (s : U → U → Prop) {n}
    (e r x y : Fin n) (v : Fin n → U) :
    Eval s (rowMatchingFormula e r x y) v ↔ RowMatching s (v e) (v r) (v x) (v y) := by
  simp only [rowMatchingFormula, Eval, eval_relatedFormula, RowMatching, cons_zero, cons_succ]
  rfl

-- Reflexive pre-fixed relations need not be symmetric or transitive.
def GraphPreFixedCode (s : U → U → Prop) (a e r : U) : Prop :=
  GraphCode s a r ∧ (∀ x, s x a → CodedRelation s r x x) ∧
    ∀ x y, s x a → s y a → RowMatching s e r x y → CodedRelation s r x y

def graphPreFixedFormula {n} (a e r : Fin n) : Formula n :=
  .conj (graphCodeFormula a r)
    (.conj (.all (.impl (.member 0 a.succ) (relatedFormula r.succ 0 0)))
      (.all (.all (.impl (.member 1 a.succ.succ)
        (.impl (.member 0 a.succ.succ)
          (.impl (rowMatchingFormula e.succ.succ r.succ.succ 1 0)
            (relatedFormula r.succ.succ 1 0)))))))

theorem eval_graphPreFixedFormula (s : U → U → Prop) {n}
    (a e r : Fin n) (v : Fin n → U) :
    Eval s (graphPreFixedFormula a e r) v ↔ GraphPreFixedCode s (v a) (v e) (v r) := by
  simp only [graphPreFixedFormula, Eval, eval_graphCodeFormula, eval_relatedFormula,
    eval_rowMatchingFormula, GraphPreFixedCode, cons_zero, cons_succ]
  rfl

def LeastGraphRelationCode (s : U → U → Prop) (a e r : U) : Prop :=
  GraphPreFixedCode s a e r ∧ ∀ k, GraphPreFixedCode s a e k →
    ∀ x y, CodedRelation s r x y → CodedRelation s k x y

theorem rowMatching_mono {e r k x y : U}
    (h : ∀ u v, CodedRelation s r u v → CodedRelation s k u v)
    (hm : RowMatching s e r x y) : RowMatching s e k x y := by
  constructor
  · intro u hu
    obtain ⟨v, hv, huv⟩ := hm.1 u hu
    exact ⟨v, hv, h u v huv⟩
  · intro v hv
    obtain ⟨u, hu, huv⟩ := hm.2 v hv
    exact ⟨u, hu, h u v huv⟩

theorem least_graph_relation_exists (base : BaseCollection s) (a e : U) :
    ∃ r, LeastGraphRelationCode s a e r := by
  obtain ⟨r, hrG, hr⟩ := normalized_relation_comprehension base
    (Formula.all (.impl (graphPreFixedFormula 3 4 0) (relatedFormula 0 2 1)))
    (cons a (cons e Fin.elim0)) a
  have hri : ∀ x y, CodedRelation s r x y ↔ s x a ∧ s y a ∧
      ∀ k, GraphPreFixedCode s a e k → CodedRelation s k x y := by
    intro x y
    have h := hr x y
    simp only [Eval, eval_graphPreFixedFormula, eval_relatedFormula] at h
    exact h
  refine ⟨r, ⟨hrG, ?_, ?_⟩, ?_⟩
  · intro x hx
    exact (hri x x).mpr ⟨hx, hx, fun k hk => hk.2.1 x hx⟩
  · intro x y hx hy hm
    refine (hri x y).mpr ⟨hx, hy, ?_⟩
    intro k hk
    apply hk.2.2 x y hx hy
    exact rowMatching_mono (fun u v huv => ((hri u v).mp huv).2.2 k hk) hm
  · intro k hk x y hxy
    exact ((hri x y).mp hxy).2.2 k hk

theorem least_graph_relation_fixed (base : BaseCollection s) {a e r : U}
    (hG : GraphCode s a e) (hr : LeastGraphRelationCode s a e r) :
    ∀ x y, CodedRelation s r x y ↔ s x a ∧ s y a ∧ RowMatching s e r x y := by
  obtain ⟨k, hkG, hk⟩ := normalized_relation_comprehension base
    (rowMatchingFormula 2 3 1 0) (cons e (cons r Fin.elim0)) a
  have hki : ∀ x y, CodedRelation s k x y ↔ s x a ∧ s y a ∧ RowMatching s e r x y := by
    intro x y
    exact (hk x y).trans (and_congr_right (fun _ =>
      and_congr_right (fun _ => eval_rowMatchingFormula s 2 3 1 0 _)))
  have hkr : ∀ x y, CodedRelation s k x y → CodedRelation s r x y := by
    intro x y hxy
    obtain ⟨hx, hy, hm⟩ := (hki x y).mp hxy
    exact hr.1.2.2 x y hx hy hm
  have hkp : GraphPreFixedCode s a e k := by
    refine ⟨hkG, ?_, ?_⟩
    · intro x hx
      refine (hki x x).mpr ⟨hx, hx, ?_, ?_⟩
      · intro y hy
        exact ⟨y, hy, hr.1.2.1 y (graphCode_endpoints hG hy).2⟩
      · intro y hy
        exact ⟨y, hy, hr.1.2.1 y (graphCode_endpoints hG hy).2⟩
    · intro x y hx hy hm
      exact (hki x y).mpr ⟨hx, hy, rowMatching_mono hkr hm⟩
  intro x y
  constructor
  · intro hxy
    exact (hki x y).mp (hr.2 k hkp x y hxy)
  · rintro ⟨hx, hy, hm⟩
    exact hr.1.2.2 x y hx hy hm

theorem least_graph_relation_symm (base : BaseCollection s) {a e r : U}
    (hr : LeastGraphRelationCode s a e r) {x y : U}
    (hxy : CodedRelation s r x y) : CodedRelation s r y x := by
  obtain ⟨k, hkG, hk⟩ := normalized_relation_comprehension base
    (relatedFormula 2 0 1) (cons r Fin.elim0) a
  have hki : ∀ u v, CodedRelation s k u v ↔ CodedRelation s r v u := by
    intro u v
    have h := hk u v
    rw [eval_relatedFormula] at h
    constructor
    · exact fun hh => (h.mp hh).2.2
    · intro hh
      have hb := graphCode_endpoints hr.1.1 hh
      exact h.mpr ⟨hb.2, hb.1, hh⟩
  have hkp : GraphPreFixedCode s a e k := by
    refine ⟨hkG, fun u hu => (hki u u).mpr (hr.1.2.1 u hu), ?_⟩
    intro u v hu hv hm
    apply (hki u v).mpr
    apply hr.1.2.2 v u hv hu
    constructor
    · intro z hvz
      obtain ⟨w, huw, hwz⟩ := hm.2 z hvz
      exact ⟨w, huw, (hki w z).mp hwz⟩
    · intro w huw
      obtain ⟨z, hvz, hwz⟩ := hm.1 w huw
      exact ⟨z, hvz, (hki w z).mp hwz⟩
  exact (hki x y).mp (hr.2 k hkp x y hxy)

-- A right-implication relation proves transitivity without ordinal recursion.
theorem least_graph_relation_trans (base : BaseCollection s) {a e r : U}
    (hG : GraphCode s a e) (hr : LeastGraphRelationCode s a e r) {x y z : U}
    (hxy : CodedRelation s r x y) (hyz : CodedRelation s r y z) : CodedRelation s r x z := by
  obtain ⟨k, hkG, hk⟩ := normalized_relation_comprehension base
    (Formula.all (.impl (.member 0 3)
      (.impl (relatedFormula 4 1 0) (relatedFormula 4 2 0))))
    (cons a (cons r Fin.elim0)) a
  have hki : ∀ u v, CodedRelation s k u v ↔ s u a ∧ s v a ∧
      ∀ w, s w a → CodedRelation s r v w → CodedRelation s r u w := by
    intro u v
    have h := hk u v
    simp only [Eval, eval_relatedFormula] at h
    exact h
  have hkp : GraphPreFixedCode s a e k := by
    refine ⟨hkG, ?_, ?_⟩
    · intro u hu
      exact (hki u u).mpr ⟨hu, hu, fun _ _ h => h⟩
    · intro u v hu hv hm
      refine (hki u v).mpr ⟨hu, hv, ?_⟩
      intro w hw hvw
      have hvwm := ((least_graph_relation_fixed base hG hr v w).mp hvw).2.2
      apply hr.1.2.2 u w hu hw
      constructor
      · intro p hup
        obtain ⟨q, hvq, hpq⟩ := hm.1 p hup
        obtain ⟨r', hwr, hqr⟩ := hvwm.1 q hvq
        exact ⟨r', hwr, ((hki p q).mp hpq).2.2 r' (graphCode_endpoints hG hwr).2 hqr⟩
      · intro r' hwr
        obtain ⟨q, hvq, hqr⟩ := hvwm.2 r' hwr
        obtain ⟨p, hup, hpq⟩ := hm.2 q hvq
        exact ⟨p, hup, ((hki p q).mp hpq).2.2 r' (graphCode_endpoints hG hwr).2 hqr⟩
  have hxky := hr.2 k hkp x y hxy
  exact ((hki x y).mp hxky).2.2 z (graphCode_endpoints hr.1.1 hyz).2 hyz

theorem least_graph_relation_preserves_parameter (base : BaseCollection s) {a e r t : U}
    (ht : TransitiveCode s t) (hend : EndExtensionCode s a e t)
    (hr : LeastGraphRelationCode s a e r) {x y : U}
    (hx : s x t) (hy : s y t) (hxy : CodedRelation s r x y) : x = y := by
  obtain ⟨k, hkG, hk⟩ := normalized_relation_comprehension base
    (Formula.impl (.conj (.member 1 2) (.member 0 2)) (.equal 1 0))
    (cons t Fin.elim0) a
  have hki : ∀ u v, CodedRelation s k u v ↔ s u a ∧ s v a ∧
      (s u t ∧ s v t → u = v) := by
    intro u v
    have h := hk u v
    simp only [Eval] at h
    exact h
  have hkp : GraphPreFixedCode s a e k := by
    refine ⟨hkG, fun u hu => (hki u u).mpr ⟨hu, hu, fun _ => rfl⟩, ?_⟩
    intro u v hu hv hm
    refine (hki u v).mpr ⟨hu, hv, ?_⟩
    rintro ⟨hut, hvt⟩
    apply base.extensional
    intro w
    constructor
    · intro hwu
      obtain ⟨z, hvz, hwz⟩ := hm.1 w ((hend.2 u hut w).mpr hwu)
      have hzv := (hend.2 v hvt z).mp hvz
      have heq := ((hki w z).mp hwz).2.2 ⟨ht u hut w hwu, ht v hvt z hzv⟩
      exact heq.symm ▸ hzv
    · intro hwv
      obtain ⟨z, huz, hzw⟩ := hm.2 w ((hend.2 v hvt w).mpr hwv)
      have hzu := (hend.2 u hut z).mp huz
      have heq := ((hki z w).mp hzw).2.2 ⟨ht u hut z hzu, ht v hvt w hwv⟩
      exact heq ▸ hzu
  exact ((hki x y).mp (hr.2 k hkp x y hxy)).2.2 ⟨hx, hy⟩

theorem least_graph_class_eq_iff (base : BaseCollection s) {a e m x y c d : U}
    (hG : GraphCode s a e) (hm : LeastGraphRelationCode s a e m)
    (hx : s x a) (_hy : s y a)
    (hc : GraphClassCode s a m x c) (hd : GraphClassCode s a m y d) :
    c = d ↔ CodedRelation s m x y := by
  constructor
  · intro heq
    have hxc := (hc x).mpr ⟨hx, hm.1.2.1 x hx⟩
    rw [heq] at hxc
    exact least_graph_relation_symm base hm ((hd x).mp hxc).2
  · intro hxy
    apply base.extensional
    intro z
    rw [hc z, hd z]
    constructor
    · rintro ⟨hz, hxz⟩
      exact ⟨hz, least_graph_relation_trans base hG hm
        (least_graph_relation_symm base hm hxy) hxz⟩
    · rintro ⟨hz, hyz⟩
      exact ⟨hz, least_graph_relation_trans base hG hm hxy hyz⟩

theorem least_graph_quotient_edge_from_representative (base : BaseCollection s)
    {a m e x c d : U} (hG : GraphCode s a e) (hm : LeastGraphRelationCode s a e m)
    (hx : s x a) (hc : GraphClassCode s a m x c) :
    GraphQuotientEdge s a m e c d ↔
      ∃ y, s y a ∧ CodedRelation s e x y ∧ GraphClassCode s a m y d := by
  constructor
  · rintro ⟨x', y', hx', hy', hc', hd', hxy'⟩
    have hxx' := (least_graph_class_eq_iff base hG hm hx hx' hc hc').mp rfl
    obtain ⟨y, hxy, hyy'⟩ := ((least_graph_relation_fixed base hG hm x x').mp hxx').2.2.2 y' hxy'
    have hy := (graphCode_endpoints hG hxy).2
    obtain ⟨d', hd⟩ := graph_class_exists base a m y
    have heq := (least_graph_class_eq_iff base hG hm hy hy' hd hd').mpr hyy'
    exact ⟨y, hy, hxy, heq ▸ hd⟩
  · rintro ⟨y, hy, hxy, hd⟩
    exact ⟨x, y, hx, hy, hc, hd, hxy⟩

theorem least_graph_quotient_extensional (base : BaseCollection s)
    {a m e b r : U} (hG : GraphCode s a e) (hm : LeastGraphRelationCode s a e m)
    (hb : ∀ c, s c b ↔ ∃ x, s x a ∧ GraphClassCode s a m x c)
    (hr : ∀ c d, CodedRelation s r c d ↔ GraphQuotientEdge s a m e c d) :
    GraphExtensionalCode s b r := by
  intro c hcb d hdb hrows
  obtain ⟨x, hx, hc⟩ := (hb c).mp hcb
  obtain ⟨y, hy, hd⟩ := (hb d).mp hdb
  apply (least_graph_class_eq_iff base hG hm hx hy hc hd).mpr
  apply hm.1.2.2 x y hx hy
  constructor
  · intro u hxu
    have hu := (graphCode_endpoints hG hxu).2
    obtain ⟨k, hk⟩ := graph_class_exists base a m u
    have hck := (hr c k).mpr ⟨x, u, hx, hu, hc, hk, hxu⟩
    have hdk := (hrows k ((hb k).mpr ⟨u, hu, hk⟩)).mp hck
    obtain ⟨v, hv, hyv, hvk⟩ :=
      (least_graph_quotient_edge_from_representative base hG hm hy hd).mp ((hr d k).mp hdk)
    exact ⟨v, hyv, (least_graph_class_eq_iff base hG hm hu hv hk hvk).mp rfl⟩
  · intro v hyv
    have hv := (graphCode_endpoints hG hyv).2
    obtain ⟨k, hk⟩ := graph_class_exists base a m v
    have hdk := (hr d k).mpr ⟨y, v, hy, hv, hd, hk, hyv⟩
    have hck := (hrows k ((hb k).mpr ⟨v, hv, hk⟩)).mpr hdk
    obtain ⟨u, hu, hxu, huk⟩ :=
      (least_graph_quotient_edge_from_representative base hG hm hx hc).mp ((hr c k).mp hck)
    exact ⟨u, hxu, (least_graph_class_eq_iff base hG hm hu hv huk hk).mp rfl⟩


theorem least_graph_quotient_preserves_parameter (base : BaseCollection s)
    {a e m t x y c d : U} (hG : GraphCode s a e)
    (hm : LeastGraphRelationCode s a e m) (ht : TransitiveCode s t)
    (hend : EndExtensionCode s a e t) (hx : s x t) (hy : s y t)
    (hc : GraphClassCode s a m x c) (hd : GraphClassCode s a m y d) :
    c = d ↔ x = y := by
  constructor
  · intro hcd
    exact least_graph_relation_preserves_parameter base ht hend hm hx hy
      ((least_graph_class_eq_iff base hG hm (hend.1 x hx) (hend.1 y hy) hc hd).mp hcd)
  · intro hxy
    subst y
    exact graph_class_unique base hc hd

theorem least_extensional_graph_quotient_exists (base : BaseCollection s)
    {a e : U} (hG : GraphCode s a e) :
    ∃ m b r, LeastGraphRelationCode s a e m ∧
      (∀ c, s c b ↔ ∃ x, s x a ∧ GraphClassCode s a m x c) ∧
      GraphCode s b r ∧
      (∀ c d, CodedRelation s r c d ↔ GraphQuotientEdge s a m e c d) ∧
      GraphExtensionalCode s b r := by
  obtain ⟨m, hm⟩ := least_graph_relation_exists base a e
  obtain ⟨b, hb⟩ := graph_class_nodes_exists base a m
  obtain ⟨r, hrG, hr⟩ := graph_quotient_edges_exists base e hb
  exact ⟨m, b, r, hm, hb, hrG, hr, least_graph_quotient_extensional base hG hm hb hr⟩

#print axioms least_extensional_graph_quotient_exists
#print axioms least_graph_quotient_preserves_parameter
#print axioms least_graph_relation_trans
#print axioms least_graph_relation_preserves_parameter
end FullBridge
