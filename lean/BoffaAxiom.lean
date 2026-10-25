import GraphLifting

namespace FullBridge
universe u
variable {U : Type u}

def TransitiveCode (s : U → U → Prop) (a : U) : Prop :=
  ∀ x, s x a → ∀ y, s y x → s y a

def GraphExtensionalCode (s : U → U → Prop) (a r : U) : Prop :=
  ∀ x, s x a → ∀ y, s y a →
    (∀ z, s z a → (CodedRelation s r x z ↔ CodedRelation s r y z)) → x = y

def InjectiveCode (s : U → U → Prop) (f : U) : Prop :=
  ∀ x y z, CodedRelation s f x z → CodedRelation s f y z → x = y

def RangeCode (s : U → U → Prop) (a f t : U) : Prop :=
  ∀ y, s y t ↔ ∃ x, s x a ∧ CodedRelation s f x y

def EndExtensionCode (s : U → U → Prop) (a r t₀ : U) : Prop :=
  Subset s t₀ a ∧ ∀ x, s x t₀ → ∀ y, CodedRelation s r x y ↔ s y x

/- Standard full Boffa extension condition in membership-graph coding.
   This is a model property, not an added Lean axiom or a proved model existence claim. -/
def BAFACode (s : U → U → Prop) : Prop :=
  ∀ t₀, TransitiveCode s t₀ → ∀ a r, GraphCode s a r →
    GraphExtensionalCode s a r → EndExtensionCode s a r t₀ →
    ∃ t f, TransitiveCode s t ∧ DecorationCode s a r f ∧ InjectiveCode s f ∧
      RangeCode s a f t ∧ ∀ x, s x t₀ → CodedRelation s f x x

def ExtensionalRealizationCode (s : U → U → Prop) : Prop :=
  ∀ a r, GraphCode s a r → GraphExtensionalCode s a r →
    ∃ f, DecorationCode s a r f ∧ InjectiveCode s f

theorem bafa_extensional_realization {s : U → U → Prop}
    (he : Empty s) (hb : BAFACode s) : ExtensionalRealizationCode s := by
  obtain ⟨e, he⟩ := he
  intro a r hG hE
  have ht : TransitiveCode s e := by
    intro x hx
    exact False.elim (he x hx)
  have hx : EndExtensionCode s a r e := by
    constructor
    · intro x hx
      exact False.elim (he x hx)
    · intro x hx
      exact False.elim (he x hx)
  obtain ⟨t, f, _, hf, hi, _, _⟩ := hb e ht a r hG hE hx
  exact ⟨f, hf, hi⟩

theorem decoration_injective_edge_reflection {s : U → U → Prop}
    {a r f x y vx vy : U} (hf : DecorationCode s a r f) (hi : InjectiveCode s f)
    (hx : s x a) (hfx : CodedRelation s f x vx) (hfy : CodedRelation s f y vy) :
    s vy vx ↔ CodedRelation s r x y := by
  constructor
  · intro h
    obtain ⟨z, _, hxz, hfz⟩ := (hf.2 x hx vx hfx vy).mp h
    have hzy := hi z y vy hfz hfy
    exact hzy ▸ hxz
  · intro h
    have hy : s y a := by
      obtain ⟨p, hpf, hpy⟩ := hfy
      obtain ⟨z, w, hza, hpzw⟩ := hf.1.1 p hpf
      obtain ⟨hyz, _⟩ := orderedPair_injective hpy hpzw
      exact hyz ▸ hza
    exact (hf.2 x hx vx hfx vy).mpr ⟨y, hy, h, hfy⟩

#print axioms bafa_extensional_realization
#print axioms decoration_injective_edge_reflection
end FullBridge
