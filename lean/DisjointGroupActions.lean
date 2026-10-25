import FreshFiniteRegularActions
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

theorem disjoint_membership_iso_union {a b c p q r : U}
    (ha : TransitiveCode s a) (hb : TransitiveCode s b)
    (hd : ∀ x, s x a → s x b → False)
    (hc : ∀ x, s x c ↔ s x a ∨ s x b)
    (hp : MembershipIsoCode s a a p) (hq : MembershipIsoCode s b b q)
    (hrmem : ∀ z, s z r ↔ s z p ∨ s z q)
    (hr : ∀ x y, CodedRelation s r x y ↔ CodedRelation s p x y ∨ CodedRelation s q x y) :
    MembershipIsoCode s c c r := by
  have dp := fun {x y} (h : CodedRelation s p x y) => coded_function_domain hp.1 h
  have dq := fun {x y} (h : CodedRelation s q x y) => coded_function_domain hq.1 h
  have rp := fun {x y} (h : CodedRelation s p x y) => (hp.2.2.1 y).mpr ⟨x, dp h, h⟩
  have rq := fun {x y} (h : CodedRelation s q x y) => (hq.2.2.1 y).mpr ⟨x, dq h, h⟩
  have hf : FunctionCode s c r := by
    constructor
    · intro z hz
      rcases (hrmem z).mp hz with hz | hz
      · obtain ⟨x, y, hx, hxy⟩ := hp.1.1 z hz
        exact ⟨x, y, (hc x).mpr (Or.inl hx), hxy⟩
      · obtain ⟨x, y, hx, hxy⟩ := hq.1.1 z hz
        exact ⟨x, y, (hc x).mpr (Or.inr hx), hxy⟩
    · intro x hx
      rcases (hc x).mp hx with hx | hx
      · obtain ⟨y, hxy, hy⟩ := hp.1.2 x hx
        refine ⟨y, (hr x y).mpr (Or.inl hxy), fun z hxz => ?_⟩
        exact ((hr x z).mp hxz).elim (hy z) (fun h => False.elim (hd x hx (dq h)))
      · obtain ⟨y, hxy, hy⟩ := hq.1.2 x hx
        refine ⟨y, (hr x y).mpr (Or.inr hxy), fun z hxz => ?_⟩
        exact ((hr x z).mp hxz).elim (fun h => False.elim (hd x (dp h) hx)) (hy z)
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro x y z hxz hyz
    rcases (hr x z).mp hxz with hxz | hxz <;> rcases (hr y z).mp hyz with hyz | hyz
    · exact hp.2.1 x y z hxz hyz
    · exact False.elim (hd z (rp hxz) (rq hyz))
    · exact False.elim (hd z (rp hyz) (rq hxz))
    · exact hq.2.1 x y z hxz hyz
  · intro y
    constructor
    · intro hy
      rcases (hc y).mp hy with hy | hy
      · obtain ⟨x, hx, hxy⟩ := (hp.2.2.1 y).mp hy
        exact ⟨x, (hc x).mpr (Or.inl hx), (hr x y).mpr (Or.inl hxy)⟩
      · obtain ⟨x, hx, hxy⟩ := (hq.2.2.1 y).mp hy
        exact ⟨x, (hc x).mpr (Or.inr hx), (hr x y).mpr (Or.inr hxy)⟩
    · rintro ⟨x, _, hxy⟩
      exact (hc y).mpr (((hr x y).mp hxy).elim (fun h => Or.inl (rp h)) (fun h => Or.inr (rq h)))
  · intro x y X Y hxX hyY
    rcases (hr x X).mp hxX with hxX | hxX <;> rcases (hr y Y).mp hyY with hyY | hyY
    · exact hp.2.2.2 x y X Y hxX hyY
    · exact ⟨fun h => False.elim (hd y (ha x (dp hxX) y h) (dq hyY)),
        fun h => False.elim (hd Y (ha X (rp hxX) Y h) (rq hyY))⟩
    · exact ⟨fun h => False.elim (hd y (dp hyY) (hb x (dq hxX) y h)),
        fun h => False.elim (hd Y (rp hyY) (hb X (rq hxX) Y h))⟩
    · exact hq.2.2.2 x y X Y hxX hyY

/-- Actual source-coded disjoint union, preserving both complete actions. -/
theorem disjoint_group_action_union (base : BaseCollection s) {I : Type v} {G : FiniteGroupData I}
    (P Q : TransitiveGroupAction s G) (hd : ∀ x, s x P.domain → s x Q.domain → False) :
    ∃ R : TransitiveGroupAction s G, GroupActionExtends P R ∧ GroupActionExtends Q R := by
  classical
  obtain ⟨c, hc⟩ := binary_union_exists base.pairing base.union P.domain Q.domain
  have hu := fun i => coded_relation_union base (P.code i) (Q.code i)
  let code := fun i => Classical.choose (hu i)
  have hm := fun i => (Classical.choose_spec (hu i)).1
  have hr := fun i => (Classical.choose_spec (hu i)).2
  have hTrans : TransitiveCode s c := by
    intro x hx y hyx
    exact (hc y).mpr (((hc x).mp hx).elim
      (fun h => Or.inl (P.transitive x h y hyx)) (fun h => Or.inr (Q.transitive x h y hyx)))
  have hIso : ∀ i, MembershipIsoCode s c c (code i) := fun i =>
    disjoint_membership_iso_union P.transitive Q.transitive hd hc (P.iso i) (Q.iso i) (hm i) (hr i)
  have hOne : ∀ x y, CodedRelation s (code G.one) x y → x = y :=
    fun x y h => ((hr G.one x y).mp h).elim (P.identity x y) (Q.identity x y)
  have hMul : ∀ i j x z, CodedRelation s (code (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (code j) x y ∧ CodedRelation s (code i) y z := by
    intro i j x z
    constructor
    · intro h
      rcases (hr (G.mul i j) x z).mp h with h | h
      · obtain ⟨y, hxy, hyz⟩ := (P.multiplication i j x z).mp h
        exact ⟨y, (hr j x y).mpr (Or.inl hxy), (hr i y z).mpr (Or.inl hyz)⟩
      · obtain ⟨y, hxy, hyz⟩ := (Q.multiplication i j x z).mp h
        exact ⟨y, (hr j x y).mpr (Or.inr hxy), (hr i y z).mpr (Or.inr hyz)⟩
    · rintro ⟨y, hxy, hyz⟩
      rcases (hr j x y).mp hxy with hxy | hxy <;> rcases (hr i y z).mp hyz with hyz | hyz
      · exact (hr (G.mul i j) x z).mpr (Or.inl ((P.multiplication i j x z).mpr ⟨y, hxy, hyz⟩))
      · exact False.elim (hd y (((P.iso j).2.2.1 y).mpr ⟨x, coded_function_domain (P.iso j).1 hxy, hxy⟩)
          (coded_function_domain (Q.iso i).1 hyz))
      · exact False.elim (hd y (coded_function_domain (P.iso i).1 hyz)
          (((Q.iso j).2.2.1 y).mpr ⟨x, coded_function_domain (Q.iso j).1 hxy, hxy⟩))
      · exact (hr (G.mul i j) x z).mpr (Or.inr ((Q.multiplication i j x z).mpr ⟨y, hxy, hyz⟩))
  exact ⟨⟨c, code, hTrans, hIso, hOne, hMul⟩,
    ⟨fun x hx => (hc x).mpr (Or.inl hx), fun i x y h => (hr i x y).mpr (Or.inl h)⟩,
    ⟨fun x hx => (hc x).mpr (Or.inr hx), fun i x y h => (hr i x y).mpr (Or.inr h)⟩⟩

#print axioms disjoint_group_action_union
end FullBridge
