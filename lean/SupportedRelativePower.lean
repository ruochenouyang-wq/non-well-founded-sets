import SupportedFullSeparation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem supported_subset_iff {swap : Nat → U → U} (x a : SupportedCarrier s swap) :
    Subset (supportedMember swap) x a ↔ Subset s x.val a.val := by
  constructor
  · intro h y hy
    exact h ⟨y, hereditary_support_member x.property hy⟩ hy
  · intro h y hy
    exact h y.val hy

theorem supported_subsets_eventually_invariant {F : U} (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x))
    (a : SupportedCarrier s S.map) :
    ∃ N, ∀ k, N ≤ k → ∀ X : SupportedCarrier s S.map,
      Subset (supportedMember S.map) (restrictedPairSwap S hc k X) a ↔
        Subset (supportedMember S.map) X a := by
  obtain ⟨N, hN⟩ := restricted_pair_swaps_eventually_fixed S hc a
  refine ⟨N, fun k hk X => ?_⟩
  have hm : ∀ x y, supportedMember S.map x y ↔
      supportedMember S.map (restrictedPairSwap S hc k x) (restrictedPairSwap S hc k y) := fun x y =>
    restricted_pair_swap_elementary S hc k (Formula.member (n := 2) 0 1) (cons x (cons y Fin.elim0))
  constructor
  · intro h y hy
    have hya := h _ ((hm y X).mp hy)
    rw [← hN k hk] at hya
    exact (hm y a).mpr hya
  · intro h y hy
    have hyX := (hm y (restrictedPairSwap S hc k X)).mp hy
    rw [restricted_pair_swap_involutive] at hyX
    have hya := (hm (restrictedPairSwap S hc k y) a).mp (h _ hyX)
    rw [restricted_pair_swap_involutive, hN k hk] at hya
    exact hya

/-- Only supported subsets are collected; ambient powersets may contain
    unsupported subsets and need not themselves be supported. -/
def SupportedPowerTraces (s : U → U → Prop) (swap : Nat → U → U) : Prop :=
  ∀ a : SupportedCarrier s swap, ∃ p, ∀ x,
    s x p ↔ HereditarilyEventuallyFixed s swap x ∧ Subset s x a.val

theorem supported_power_trace_hereditary (base : BaseCollection s) {F : U}
    (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x))
    (a : SupportedCarrier s S.map) {p : U}
    (hp : ∀ x, s x p ↔ HereditarilyEventuallyFixed s S.map x ∧ Subset s x a.val) :
    HereditarilyEventuallyFixed s S.map p := by
  apply supported_trace_hereditary base S hc
    (P := fun X => Subset (supportedMember S.map) X a)
  · intro x
    constructor
    · intro hx
      obtain ⟨hH, hsub⟩ := (hp x).mp hx
      exact ⟨⟨x, hH⟩, rfl, (supported_subset_iff _ a).mpr hsub⟩
    · rintro ⟨X, rfl, hsub⟩
      exact (hp X.val).mpr ⟨X.property, (supported_subset_iff X a).mp hsub⟩
  · exact supported_subsets_eventually_invariant S hc a

theorem supported_power_iff_traces (base : BaseCollection s) {F : U}
    (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) :
    PowerSet (supportedMember (s := s) S.map) ↔ SupportedPowerTraces s S.map := by
  constructor
  · intro h a
    obtain ⟨p, hp⟩ := h a
    refine ⟨p.val, fun x => ?_⟩
    constructor
    · intro hx
      let X : SupportedCarrier s S.map := ⟨x, hereditary_support_member p.property hx⟩
      exact ⟨X.property, (supported_subset_iff X a).mp ((hp X).mp hx)⟩
    · rintro ⟨hH, hsub⟩
      exact (hp ⟨x, hH⟩).mpr ((supported_subset_iff _ a).mpr hsub)
  · intro h a
    obtain ⟨p, hp⟩ := h a
    refine ⟨⟨p, supported_power_trace_hereditary base S hc a hp⟩, fun X => ?_⟩
    exact (hp X.val).trans ⟨fun h => (supported_subset_iff X a).mpr h.2,
      fun h => ⟨X.property, (supported_subset_iff X a).mp h⟩⟩

/-- A sufficient additional hypothesis, not derived from BaseCollection:
    every ambient set admits its exact trace on the hereditary carrier. -/
def SupportedBoundedAmenability (s : U → U → Prop) (swap : Nat → U → U) : Prop :=
  ∀ a, ∃ b, ∀ x, s x b ↔ s x a ∧ HereditarilyEventuallyFixed s swap x

theorem supported_power_of_bounded_amenability (base : BaseCollection s) {F : U}
    (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x))
    (ha : SupportedBoundedAmenability s S.map) : PowerSet (supportedMember (s := s) S.map) := by
  apply (supported_power_iff_traces base S hc).mpr
  intro a
  obtain ⟨p, hp⟩ := base.powerset a.val
  obtain ⟨b, hb⟩ := ha p
  exact ⟨b, fun x => (hb x).trans ((and_congr (hp x) Iff.rfl).trans and_comm)⟩

#print axioms supported_power_iff_traces
#print axioms supported_power_of_bounded_amenability
end FullBridge
