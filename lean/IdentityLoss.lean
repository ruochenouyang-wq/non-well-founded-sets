import ChoiceModelBridge
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def SelfSingleton (s : U → U → Prop) (a : U) : Prop := ∀ x, s x a ↔ x = a

theorem selfSingleton_same_code (base : BaseCollection s) {a b : U}
    (ha : SelfSingleton s a) (hb : SelfSingleton s b) :
    internalCode base a = internalCode base b := by
  obtain ⟨r, hr⟩ := codedRelation_singleton base.pairing a b
  apply (internal_code_eq base a b).mpr
  refine ⟨r, ?_, Or.inr ((hr a b).mpr ⟨rfl, rfl⟩)⟩
  intro x y hxy
  rcases hxy with rfl | hxy
  · exact ⟨fun z hz => ⟨z, hz, Or.inl rfl⟩, fun z hz => ⟨z, hz, Or.inl rfl⟩⟩
  obtain ⟨hx, hy⟩ := (hr x y).mp hxy
  subst x
  subst y
  constructor
  · intro z hz
    have hza := (ha z).mp hz
    subst z
    exact ⟨b, (hb b).mpr rfl, Or.inr ((hr a b).mpr ⟨rfl, rfl⟩)⟩
  · intro z hz
    have hzb := (hb z).mp hz
    subst z
    exact ⟨a, (ha a).mpr rfl, Or.inr ((hr a b).mpr ⟨rfl, rfl⟩)⟩

theorem bafa_selfSingleton_family (base : BaseCollection s) (hBAFA : BAFACode s) (a : U) :
    ∃ f, FunctionCode s a f ∧ InjectiveCode s f ∧
      ∀ x v, s x a → CodedRelation s f x v → SelfSingleton s v := by
  obtain ⟨e, heG, he⟩ := normalized_relation_comprehension base
    (Formula.equal (n := 2) 0 1) Fin.elim0 a
  have hei : ∀ x y, CodedRelation s e x y ↔ s x a ∧ s y a ∧ y = x := by
    intro x y
    exact he x y
  have hext : GraphExtensionalCode s a e := by
    intro x hx y hy hrows
    have hyx := (hrows x hx).mp ((hei x x).mpr ⟨hx, hx, rfl⟩)
    exact (hei y x).mp hyx |>.2.2
  obtain ⟨f, hf, hfi⟩ := bafa_extensional_realization base.empty hBAFA a e heG hext
  refine ⟨f, hf.1, hfi, ?_⟩
  intro x v hx hxv w
  constructor
  · intro hw
    obtain ⟨y, _, hexy, hfyw⟩ := (hf.2 x hx v hxv w).mp hw
    have hyx := (hei x y).mp hexy |>.2.2
    subst y
    obtain ⟨v₀, _, hu⟩ := hf.1.2 x hx
    exact (hu w hfyw).trans (hu v hxv).symm
  · intro hwv
    subst w
    exact (hf.2 x hx v hxv v).mpr ⟨x, hx, (hei x x).mpr ⟨hx, hx, rfl⟩, hxv⟩

theorem bafa_family_collapses (base : BaseCollection s) (hBAFA : BAFACode s) (a : U) :
    ∃ f, FunctionCode s a f ∧ InjectiveCode s f ∧
      (∀ x v, s x a → CodedRelation s f x v → SelfSingleton s v) ∧
      ∀ x y v w, s x a → s y a → CodedRelation s f x v → CodedRelation s f y w →
        internalCode base v = internalCode base w := by
  obtain ⟨f, hf, hi, hs⟩ := bafa_selfSingleton_family base hBAFA a
  exact ⟨f, hf, hi, hs, fun x y v w hx hy hxv hyw =>
    selfSingleton_same_code base (hs x v hx hxv) (hs y w hy hyw)⟩

theorem bafa_distinct_selfSingletons (base : BaseCollection s) (hBAFA : BAFACode s) :
    ∃ v w, v ≠ w ∧ SelfSingleton s v ∧ SelfSingleton s w := by
  obtain ⟨e, he⟩ := base.empty
  obtain ⟨p, hp⟩ := base.pairing e e
  have hpe : p ≠ e := by
    intro h
    have hep := (hp e).mpr (Or.inl rfl)
    rw [h] at hep
    exact he e hep
  obtain ⟨a, ha⟩ := base.pairing e p
  have hea := (ha e).mpr (Or.inl rfl)
  have hpa := (ha p).mpr (Or.inr rfl)
  obtain ⟨f, hf, hi, hs⟩ := bafa_selfSingleton_family base hBAFA a
  obtain ⟨v, hev, _⟩ := hf.2 e hea
  obtain ⟨w, hpw, _⟩ := hf.2 p hpa
  refine ⟨v, w, ?_, hs e v hea hev, hs p w hpa hpw⟩
  intro hvw
  subst w
  exact hpe (hi p e v hpw hev)

theorem bridge_not_injective (base : BaseCollection s) (hBAFA : BAFACode s) :
    ∃ v w, v ≠ w ∧ internalCode base v = internalCode base w := by
  obtain ⟨v, w, hne, hv, hw⟩ := bafa_distinct_selfSingletons base hBAFA
  exact ⟨v, w, hne, selfSingleton_same_code base hv hw⟩

theorem bridge_not_membership_reflecting (base : BaseCollection s) (hBAFA : BAFACode s) :
    ∃ v w, ¬s w v ∧ internalMember base (internalCode base w) (internalCode base v) := by
  obtain ⟨v, w, hne, hv, hw⟩ := bafa_distinct_selfSingletons base hBAFA
  refine ⟨v, w, (fun hwv => hne ((hv w).mp hwv).symm), ?_⟩
  exact (internal_exact_members base v (internalCode base w)).mpr
    ⟨v, (hv v).mpr rfl, selfSingleton_same_code base hv hw⟩

#print axioms bafa_family_collapses
#print axioms bridge_not_membership_reflecting
end FullBridge
