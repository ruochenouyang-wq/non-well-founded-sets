import InternalFoundation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- E is an external relation parameter; no first-order definability is asserted. -/
def HomogeneousChoiceCode (s E : U → U → Prop) : Prop :=
  ∀ a, (∀ c, s c a → (∃ x, s x c) ∧ (∀ y z, s y c → s z c → E y z)) →
    ∃ f, ChoiceFunctionCode s a f

/-- Each row selects actual members and is E-homogeneous; different rows need not coordinate. -/
def HomogeneousSelectionRelation (s E : U → U → Prop) (a r : U) : Prop :=
  (∀ p, s p r → ∃ x y, s x a ∧ IsOrderedPair s p x y) ∧
  (∀ x, s x a → ∃ y, CodedRelation s r x y) ∧
  (∀ x y, CodedRelation s r x y → s y x) ∧
  ∀ x y z, CodedRelation s r x y → CodedRelation s r x z → E y z

def HomogeneousSelectionCode (s E : U → U → Prop) : Prop :=
  ∀ a, (∀ x, s x a → ∃ y, s y x) → ∃ r, HomogeneousSelectionRelation s E a r

theorem homogeneous_choice_resolves_relation (base : BaseCollection s)
    (E : U → U → Prop) (hFC : HomogeneousChoiceCode s E)
    {a r : U} (hr : HomogeneousSelectionRelation s E a r) :
    ∃ f, ChoiceFunctionCode s a f ∧
      ∀ x y, CodedRelation s f x y → CodedRelation s r x y := by
  obtain ⟨b, hb⟩ := relation_row_family base a r
  have hbh : ∀ c, s c b → (∃ y, s y c) ∧ (∀ y z, s y c → s z c → E y z) := by
    intro c hc
    obtain ⟨x, hx, hrow⟩ := (hb c).mp hc
    constructor
    · obtain ⟨y, hxy⟩ := hr.2.1 x hx
      exact ⟨y, (hrow y).mpr hxy⟩
    · intro y z hy hz
      exact hr.2.2.2 x y z
        ((hrow y).mp hy) ((hrow z).mp hz)
  obtain ⟨k, hk⟩ := hFC b hbh
  obtain ⟨u, hu⟩ := base.union a
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union a u
  obtain ⟨f, hf⟩ := relation_comprehension_members base resolvedChoiceFormula
    (cons a (cons r (cons k Fin.elim0))) d
  have selected : ∀ x y, s x a →
      (∃ c, RelationRow s r x c ∧ CodedRelation s k c y) → CodedRelation s r x y := by
    rintro x y hx ⟨c, hc, hkcy⟩
    exact (hc y).mp (hk.2 c ((hb c).mpr ⟨x, hx, hc⟩) y hkcy)
  have hn : ∀ p, s p f → ∃ x y, s x a ∧ IsOrderedPair s p x y := by
    intro p hp
    obtain ⟨x, y, _, _, hpxy, hev⟩ := (hf p).mp hp
    exact ⟨x, y, ((eval_resolvedChoiceFormula s y x a r k).mp hev).1, hpxy⟩
  have hi : ∀ x y, CodedRelation s f x y ↔ s x a ∧
      ∃ c, RelationRow s r x c ∧ CodedRelation s k c y := by
    intro x y
    constructor
    · rintro ⟨p, hp, hpxy⟩
      obtain ⟨x', y', _, _, hp', hev⟩ := (hf p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxy hp'
      exact (eval_resolvedChoiceFormula s y x a r k).mp hev
    · rintro ⟨hx, hw⟩
      have hyx := hr.2.2.1 x y (selected x y hx hw)
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x y
      exact ⟨p, (hf p).mpr ⟨x, y, (hd x).mpr (Or.inl hx),
        (hd y).mpr (Or.inr ((hu y).mpr ⟨x, hx, hyx⟩)), hp,
        (eval_resolvedChoiceFormula s y x a r k).mpr ⟨hx, hw⟩⟩, hp⟩
  have hsub : ∀ x y, CodedRelation s f x y → CodedRelation s r x y := by
    intro x y hxy
    exact selected x y ((hi x y).mp hxy).1 ((hi x y).mp hxy).2
  refine ⟨f, ⟨⟨hn, ?_⟩, ?_⟩, hsub⟩
  · intro x hx
    obtain ⟨c, hc⟩ := relation_row_exists base r x
    have hcb := (hb c).mpr ⟨x, hx, hc⟩
    obtain ⟨y, hky, huniq⟩ := hk.1.2 c hcb
    refine ⟨y, (hi x y).mpr ⟨hx, c, hc, hky⟩, ?_⟩
    intro z hxz
    obtain ⟨_, c', hc', hkz⟩ := (hi x z).mp hxz
    have heq := relation_row_unique base hc' hc
    subst c'
    exact huniq z hkz
  · intro x _ y hxy
    exact hr.2.2.1 x y (hsub x y hxy)

theorem choice_implies_homogeneous_selection (E : U → U → Prop)
    (hE : ∀ x, E x x) (hAC : ChoiceCode s) : HomogeneousSelectionCode s E := by
  intro a ha
  obtain ⟨f, hf⟩ := hAC a ha
  refine ⟨f, hf.1.1, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, _⟩ := hf.1.2 x hx
    exact ⟨y, hy⟩
  · intro x y hxy
    obtain ⟨p, hp, hpair⟩ := hxy
    obtain ⟨x', y', hx', hpair'⟩ := hf.1.1 p hp
    obtain ⟨rfl, rfl⟩ := orderedPair_injective hpair hpair'
    exact hf.2 x hx' y ⟨p, hp, hpair⟩
  · intro x y z hxy hxz
    obtain ⟨p, hp, hpair⟩ := hxy
    obtain ⟨x', y', hx', hpair'⟩ := hf.1.1 p hp
    obtain ⟨rfl, rfl⟩ := orderedPair_injective hpair hpair'
    obtain ⟨w, _, hu⟩ := hf.1.2 x hx'
    have hyz := (hu y ⟨p, hp, hpair⟩).trans (hu z hxz).symm
    exact hyz ▸ hE y

theorem choice_iff_homogeneous_factorization (base : BaseCollection s)
    (E : U → U → Prop) (hE : ∀ x, E x x) :
    ChoiceCode s ↔ HomogeneousSelectionCode s E ∧ HomogeneousChoiceCode s E := by
  constructor
  · intro hAC
    exact ⟨choice_implies_homogeneous_selection E hE hAC,
      fun a ha => hAC a (fun c hc => (ha c hc).1)⟩
  · rintro ⟨hS, hC⟩ a ha
    obtain ⟨r, hr⟩ := hS a ha
    obtain ⟨f, hf, _⟩ := homogeneous_choice_resolves_relation base E hC hr
    exact ⟨f, hf⟩

theorem behavior_selection_is_homogeneous (base : BaseCollection s) {a r : U}
    (hr : BehaviorChoiceRelation s a r) :
    HomogeneousSelectionRelation s (InternalBehavior s) a r := by
  exact ⟨hr.1, hr.2.1, hr.2.2.1,
    fun x y z hxy hxz => hr.2.2.2 x x y z (internalBehavior_refl base.empty x) hxy hxz⟩

theorem fiber_choice_is_homogeneous_choice :
    FiberChoiceCode s ↔ HomogeneousChoiceCode s (InternalBehavior s) := by
  rfl

/-- A second proof: the refinement half of the behavior split is generic row selection. -/
theorem behavior_choice_split_via_homogeneous (base : BaseCollection s) :
    ChoiceCode s ↔ BehaviorChoiceCode s ∧ FiberChoiceCode s := by
  constructor
  · intro hAC
    exact ⟨source_choice_implies_behavior_choice base hAC,
      fun a ha => hAC a (fun c hc => (ha c hc).1)⟩
  · rintro ⟨hBC, hFC⟩
    apply (choice_iff_homogeneous_factorization base (InternalBehavior s)
      (internalBehavior_refl base.empty)).mpr
    refine ⟨?_, fiber_choice_is_homogeneous_choice.mp hFC⟩
    intro a ha
    obtain ⟨r, hr⟩ := hBC a ha
    exact ⟨r, behavior_selection_is_homogeneous base hr⟩

#print axioms choice_iff_homogeneous_factorization
#print axioms behavior_choice_split_via_homogeneous
end FullBridge
