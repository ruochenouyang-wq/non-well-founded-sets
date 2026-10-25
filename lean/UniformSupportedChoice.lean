import UniformSupportedPowers
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop} {swap : Nat → U → U}

theorem uniform_support_ordered_pair (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} {x y p : U} (hx : UniformHereditarySupport s swap N x)
    (hy : UniformHereditarySupport s swap N y) (hp : IsOrderedPair s p x y) :
    UniformHereditarySupport s swap N p := by
  obtain ⟨a, b, ha, hb, hp⟩ := hp
  exact uniform_support_pair base hj ho
    (uniform_support_pair base hj ho hx hx ha) (uniform_support_pair base hj ho hx hy hb) hp

/-- Every actual selector of a uniformly supported family has the same
    uniform support bound; no choice axiom is used to prove this. -/
theorem uniform_support_choice_function (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} {a f : U} (ha : UniformHereditarySupport s swap N a)
    (hf : ChoiceFunctionCode s a f) : UniformHereditarySupport s swap N f := by
  apply uniform_support_of_members base hj ho
  intro p hp
  obtain ⟨x, y, hx, hpxy⟩ := hf.1.1 p hp
  have hyx := hf.2 x hx y ⟨p, hp, hpxy⟩
  have hX := uniform_support_member ha hx
  exact uniform_support_ordered_pair base hj ho hX (uniform_support_member hX hyx) hpxy

theorem ambient_choice_function_supported (a f : SupportedCarrier s swap)
    (hf : ChoiceFunctionCode s a.val f.val) : ChoiceFunctionCode (supportedMember swap) a f := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨x, y, hx, hpxy⟩ := hf.1.1 p.val hp
    let X : SupportedCarrier s swap := ⟨x, hereditary_support_member a.property hx⟩
    let Y : SupportedCarrier s swap := ⟨y, (supported_relation_components f.property ⟨p.val, hp, hpxy⟩).2⟩
    exact ⟨X, Y, hx, (supported_ordered_pair_iff p X Y).mpr hpxy⟩
  · intro x hx
    obtain ⟨y, hxy, hy⟩ := hf.1.2 x.val hx
    let Y : SupportedCarrier s swap := ⟨y, (supported_relation_components f.property hxy).2⟩
    exact ⟨Y, (supported_coded_relation_iff f x Y).mpr hxy,
      fun z hz => Subtype.ext (hy z.val ((supported_coded_relation_iff f x z).mp hz))⟩
  · intro x hx y hxy
    exact hf.2 x.val hx y.val ((supported_coded_relation_iff f x y).mp hxy)

/-- Hence a source selector cannot be lost on a uniformly supported
    family. This is a local equivalence, not an assumption of source AC. -/
theorem supported_uniform_selector_iff (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} (a : SupportedCarrier s swap) (ha : UniformHereditarySupport s swap N a.val) :
    (∃ f : SupportedCarrier s swap, ChoiceFunctionCode (supportedMember swap) a f) ↔
      ∃ f, ChoiceFunctionCode s a.val f := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.val, supported_choice_function_ambient a f hf⟩
  · rintro ⟨f, hf⟩
    have hF := uniform_support_hereditary (uniform_support_choice_function base hj ho ha hf)
    exact ⟨⟨f, hF⟩, ambient_choice_function_supported a ⟨f, hF⟩ hf⟩

theorem supported_uniform_family_choice (base : BaseCollection s) (hAC : ChoiceCode s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} (a : SupportedCarrier s swap) (ha : UniformHereditarySupport s swap N a.val)
    (hne : ∀ x, supportedMember swap x a → ∃ y, supportedMember swap y x) :
    ∃ f : SupportedCarrier s swap, ChoiceFunctionCode (supportedMember swap) a f := by
  apply (supported_uniform_selector_iff base hj ho a ha).mpr
  apply hAC a.val
  intro x hx
  obtain ⟨y, hy⟩ := hne ⟨x, hereditary_support_member a.property hx⟩ hx
  exact ⟨y.val, hy⟩

/-- The actual no-choice family has hereditary support but no common
    descendant bound. Strengthening the carrier to uniform support loses F. -/
theorem pair_sequence_family_not_uniform {F : U} (S : PairSwapSequence s F) :
    ¬ ∃ N, UniformHereditarySupport s S.map N F := by
  rintro ⟨N, hN⟩
  have hrow := uniform_support_member hN (S.row_mem N)
  have hleft := uniform_support_member hrow ((S.action N).pair _ |>.mpr (Or.inl rfl))
  have hfix := uniform_support_root hleft N (Nat.le_refl N)
  change (S.action N).map (S.action N).left = (S.action N).left at hfix
  rw [(S.action N).swap_left] at hfix
  exact (S.action N).distinct hfix.symm

theorem countable_bafa_supported_powers_and_unbounded_support
    (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ F, ∃ S : PairSwapSequence s F,
      (∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) ∧
      HereditarilyEventuallyFixed s S.map F ∧
      (¬ ∃ N, UniformHereditarySupport s S.map N F) ∧
      ¬ ChoiceCode (supportedMember (s := s) S.map) ∧
      (∃ z w, OmegaCode s z w ∧ ∃ T : Nat → SupportedCarrier s S.map,
        (T 0).val = w ∧
        (∀ k, UniformHereditarySupport s S.map 0 (T k).val) ∧
        (∀ k x, s x (T (k+1)).val ↔ Subset s x (T k).val) ∧
        (∀ k X, supportedMember S.map X (T (k+1)) ↔ Subset (supportedMember S.map) X (T k))) := by
  obtain ⟨F, S, hc⟩ := countable_bafa_commuting_pair_sequence base hB enum henum
  exact ⟨F, S, hc, pair_sequence_family_hereditarily_supported S,
    pair_sequence_family_not_uniform S, pair_sequence_supported_carrier_not_choice S,
    supported_internal_omega_power_tower base (fun n => (S.action n).elementary)
      (fun n => (S.action n).onto) (fun n => (S.action n).locally_internal)⟩

#print axioms supported_uniform_selector_iff
#print axioms countable_bafa_supported_powers_and_unbounded_support
end FullBridge
