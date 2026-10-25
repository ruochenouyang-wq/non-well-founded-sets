import SupportedTraces
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Truth is evaluated in the subtype, including its unbounded quantifiers. -/
def SupportedSeparationTraces (s : U → U → Prop) (swap : Nat → U → U) : Prop :=
  ∀ n (p : Formula (n+1)) (v : Fin n → SupportedCarrier s swap) (a : SupportedCarrier s swap),
    ∃ b, SupportedTrace swap
      (fun X => supportedMember swap X a ∧ Eval (supportedMember swap) p (cons X v)) b

theorem supported_formula_subset_eventually_invariant {F : U} (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x))
    {n} (p : Formula (n+1)) (v : Fin n → SupportedCarrier s S.map)
    (a : SupportedCarrier s S.map) :
    ∃ N, ∀ k, N ≤ k → ∀ X : SupportedCarrier s S.map,
      (supportedMember S.map (restrictedPairSwap S hc k X) a ∧
        Eval (supportedMember S.map) p (cons (restrictedPairSwap S hc k X) v)) ↔
      (supportedMember S.map X a ∧ Eval (supportedMember S.map) p (cons X v)) := by
  obtain ⟨N, hN⟩ := restricted_pair_swaps_eventually_fixed S hc a
  obtain ⟨M, hM⟩ := eventually_fixed_finite_parameters v
    (fun i => restricted_pair_swaps_eventually_fixed S hc (v i))
  refine ⟨max N M, fun k hk X => ?_⟩
  have ha := hN k (Nat.le_trans (Nat.le_max_left N M) hk)
  have hv := hM k (Nat.le_trans (Nat.le_max_right N M) hk)
  have hm : supportedMember S.map X a ↔
      supportedMember S.map (restrictedPairSwap S hc k X) (restrictedPairSwap S hc k a) :=
    restricted_pair_swap_elementary S hc k (Formula.member (n := 2) 0 1) (cons X (cons a Fin.elim0))
  rw [ha] at hm
  have he : (fun i => restrictedPairSwap S hc k (cons X v i)) = cons (restrictedPairSwap S hc k X) v := by
    funext i
    exact Fin.cases rfl (fun j => hv j) i
  have hp := restricted_pair_swap_elementary S hc k p (cons X v)
  rw [he] at hp
  exact and_congr hm.symm hp.symm

theorem supported_full_separation_of_traces (base : BaseCollection s) {F : U}
    (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x))
    (ht : SupportedSeparationTraces s S.map) : Separation (supportedMember (s := s) S.map) := by
  intro n p v a
  obtain ⟨b, hb⟩ := ht n p v a
  have hB := supported_trace_hereditary base S hc hb
    (supported_formula_subset_eventually_invariant S hc p v a)
  exact ⟨⟨b, hB⟩, fun X => supported_trace_member hb X⟩

/-- Exact remaining existence obligation. This is not an assertion that
    the obligation has been discharged for the constructed candidate. -/
theorem supported_full_separation_iff_traces (base : BaseCollection s) {F : U}
    (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) :
    Separation (supportedMember (s := s) S.map) ↔ SupportedSeparationTraces s S.map := by
  constructor
  · intro hs n p v a
    obtain ⟨b, hb⟩ := hs n p v a
    refine ⟨b.val, fun x => ?_⟩
    constructor
    · intro hx
      let X : SupportedCarrier s S.map := ⟨x, hereditary_support_member b.property hx⟩
      exact ⟨X, rfl, (hb X).mp hx⟩
    · rintro ⟨X, rfl, hp⟩
      exact (hb X).mpr hp
  · exact supported_full_separation_of_traces base S hc

#print axioms supported_full_separation_iff_traces
end FullBridge
