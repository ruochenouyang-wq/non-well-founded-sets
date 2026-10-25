import TheorySeparation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Compatibility across every pair of parameter sets, including equal ones. -/
def ParameterFamilyCompatible (base : BaseCollection s) (F : U) : Prop :=
  ∀ a b x y, s a F → s b F → s x a → s y b →
    internalCode base x = internalCode base y → x = y

theorem parameter_family_union_criterion (base : BaseCollection s) {F d : U}
    (hd : ∀ x, s x d ↔ ∃ a, s a F ∧ s x a) :
    ParameterInjective base d ↔ ParameterFamilyCompatible base F := by
  constructor
  · intro hi a b x y ha hb hx hy hxy
    exact hi x y ((hd x).mpr ⟨a, ha, hx⟩) ((hd y).mpr ⟨b, hb, hy⟩) hxy
  · intro hc x y hx hy hxy
    obtain ⟨a, ha, hxa⟩ := (hd x).mp hx
    obtain ⟨b, hb, hyb⟩ := (hd y).mp hy
    exact hc a b x y ha hb hxa hyb hxy

theorem transitive_parameter_family_union {F d : U}
    (hd : ∀ x, s x d ↔ ∃ a, s a F ∧ s x a)
    (hF : ∀ a, s a F → TransitiveCode s a) : TransitiveCode s d := by
  intro x hx y hy
  obtain ⟨a, ha, hxa⟩ := (hd x).mp hx
  exact (hd y).mpr ⟨a, ha, hF a ha x hxa y hy⟩

theorem simultaneous_parameter_extension_iff (base : BaseCollection s)
    (hBAFA : BAFACode s) (hAC : ChoiceCode s) (F : U)
    (hF : ∀ a, s a F → TransitiveCode s a)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (hFB : ∀ a, s a F → Subset (internalMember base) (internalCode base a) B) :
    (∃ T, TransitiveCode s T ∧ (∀ a, s a F → Subset s a T) ∧
      internalCode base T = B ∧ ParameterInjective base T) ↔
      ParameterFamilyCompatible base F := by
  constructor
  · rintro ⟨T, _, hFT, _, hi⟩ a b x y ha hb hx hy hxy
    exact hi x y (hFT a ha x hx) (hFT b hb y hy) hxy
  · intro hc
    obtain ⟨d, hd⟩ := base.union F
    have hdT := transitive_parameter_family_union hd hF
    have hi := (parameter_family_union_criterion base hd).mpr hc
    have hdB : Subset (internalMember base) (internalCode base d) B := by
      intro X hX
      obtain ⟨x, hx, rfl⟩ := (internal_exact_members base d X).mp hX
      obtain ⟨a, ha, hxa⟩ := (hd x).mp hx
      exact hFB a ha _ ((internal_exact_members base a _).mpr ⟨x, hxa, rfl⟩)
    obtain ⟨T, hT, hdT', hTB, hTi⟩ := relative_parameter_extension base hBAFA hAC hdT hi B hB hdB
    exact ⟨T, hT, fun a ha x hx => hdT' x ((hd x).mpr ⟨a, ha, hx⟩), hTB, hTi⟩

theorem bafa_incompatible_preservable_parameters (base : BaseCollection s)
    (hBAFA : BAFACode s) :
    ∃ a b, TransitiveCode s a ∧ TransitiveCode s b ∧
      ParameterInjective base a ∧ ParameterInjective base b ∧
      ¬∃ T, Subset s a T ∧ Subset s b T ∧ ParameterInjective base T := by
  obtain ⟨a, b, hne, ha, hb⟩ := bafa_distinct_selfSingletons base hBAFA
  obtain ⟨haT, hai, _⟩ := selfSingleton_parameter_preserved base ha
  obtain ⟨hbT, hbi, _⟩ := selfSingleton_parameter_preserved base hb
  refine ⟨a, b, haT, hbT, hai, hbi, ?_⟩
  rintro ⟨T, haT', hbT', hi⟩
  exact hne (hi a b (haT' a ((ha a).mpr rfl)) (hbT' b ((hb b).mpr rfl))
    (selfSingleton_same_code base ha hb))

#print axioms simultaneous_parameter_extension_iff
#print axioms bafa_incompatible_preservable_parameters
end FullBridge
