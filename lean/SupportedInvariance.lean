import GlobalPairBitActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem member_descendant_map {j : U → U} (hm : ∀ x y, s x y → s (j x) (j y))
    {x y : U} (h : MemberDescendant s x y) : MemberDescendant s (j x) (j y) := by
  induction h with
  | refl => exact .refl _
  | step hxy _ ih => exact .step (hm _ _ hxy) ih

theorem hereditary_support_commuting_involution {swap : Nat → U → U} {j : U → U}
    (hm : ∀ x y, s x y → s (j x) (j y)) (hs : ∀ x, j (j x) = x)
    (hc : ∀ n x, swap n (j x) = j (swap n x)) {x : U}
    (hx : HereditarilyEventuallyFixed s swap x) : HereditarilyEventuallyFixed s swap (j x) := by
  intro y hy
  have hdesc := member_descendant_map hm hy
  rw [hs x] at hdesc
  obtain ⟨N, hN⟩ := hx (j y) hdesc
  refine ⟨N, fun n hn => ?_⟩
  have he : j (swap n y) = j y := (hc n y).symm.trans (hN n hn)
  exact (hs (swap n y)).symm.trans ((congrArg j he).trans (hs y))

theorem pair_sequence_support_invariant {F : U} (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) (n : Nat) (x : U) :
    HereditarilyEventuallyFixed s S.map (S.map n x) ↔ HereditarilyEventuallyFixed s S.map x := by
  have hm : ∀ x y, s x y → s (S.map n x) (S.map n y) := fun x y h =>
    ((S.action n).elementary (Formula.member (n := 2) 0 1) (cons x (cons y Fin.elim0))).mp h
  have hs : ∀ x, S.map n (S.map n x) = x := (S.action n).involutive
  have hforward := fun {x} => hereditary_support_commuting_involution hm hs (fun k x => hc k n x) (x := x)
  exact ⟨fun h => hs x ▸ hforward h, fun h => hforward h⟩

def restrictedPairSwap {F : U} (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) (n : Nat)
    (x : SupportedCarrier s S.map) : SupportedCarrier s S.map :=
  ⟨S.map n x.val, (pair_sequence_support_invariant S hc n x.val).mpr x.property⟩

theorem restricted_pair_swap_involutive {F : U} (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) (n : Nat)
    (x : SupportedCarrier s S.map) : restrictedPairSwap S hc n (restrictedPairSwap S hc n x) = x :=
  Subtype.ext ((S.action n).involutive x.val)

theorem restricted_pair_swap_elementary {F : U} (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) (n : Nat) :
    ElementaryMap (supportedMember S.map) (supportedMember S.map) (restrictedPairSwap S hc n) := by
  apply bijective_membership_elementary
  · intro x y he
    exact (restricted_pair_swap_involutive S hc n x).symm.trans
      ((congrArg (restrictedPairSwap S hc n) he).trans (restricted_pair_swap_involutive S hc n y))
  · intro y
    exact ⟨restrictedPairSwap S hc n y, restricted_pair_swap_involutive S hc n y⟩
  · intro x y
    exact (S.action n).elementary (Formula.member (n := 2) 0 1) (cons x.val (cons y.val Fin.elim0))

theorem restricted_pair_swaps_commute {F : U} (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) (n m : Nat)
    (x : SupportedCarrier s S.map) :
    restrictedPairSwap S hc n (restrictedPairSwap S hc m x) =
      restrictedPairSwap S hc m (restrictedPairSwap S hc n x) := Subtype.ext (hc n m x.val)

theorem restricted_pair_swaps_eventually_fixed {F : U} (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) (x : SupportedCarrier s S.map) :
    ∃ N, ∀ n, N ≤ n → restrictedPairSwap S hc n x = x := by
  obtain ⟨N, hN⟩ := hereditary_support_root x.property
  exact ⟨N, fun n hn => Subtype.ext (hN n hn)⟩

/-- An actual invariant candidate with commuting global swaps and verified
    basic axioms, bounded Separation and failed Choice. The remaining full
    model axioms are still not asserted. -/
theorem countable_bafa_invariant_supported_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ F, ∃ S : PairSwapSequence s F,
      (∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) ∧
      HereditarilyEventuallyFixed s S.map F ∧
      Extensional (supportedMember (s := s) S.map) ∧ Empty (supportedMember (s := s) S.map) ∧
      Pairing (supportedMember (s := s) S.map) ∧ Union (supportedMember (s := s) S.map) ∧
      Infinity (supportedMember (s := s) S.map) ∧ BoundedSeparation (supportedMember (s := s) S.map) ∧
      ¬ ChoiceCode (supportedMember (s := s) S.map) ∧
      (∀ n x, HereditarilyEventuallyFixed s S.map (S.map n x) ↔ HereditarilyEventuallyFixed s S.map x) := by
  obtain ⟨F, S, hc⟩ := countable_bafa_commuting_pair_sequence base hB enum henum
  exact ⟨F, S, hc, pair_sequence_family_hereditarily_supported S,
    supported_carrier_extensional base.extensional S.map,
    supported_carrier_empty base S.map (fun n => (S.action n).elementary) (fun n => (S.action n).onto),
    supported_carrier_pairing base S.map (fun n => (S.action n).elementary),
    supported_carrier_union base S.map (fun n => (S.action n).elementary) (fun n => (S.action n).onto),
    supported_carrier_infinity base S.map (fun n => (S.action n).locally_internal),
    supported_carrier_bounded_separation base S.map (fun n => (S.action n).elementary) (fun n => (S.action n).onto),
    pair_sequence_supported_carrier_not_choice S, pair_sequence_support_invariant S hc⟩

#print axioms countable_bafa_invariant_supported_candidate
end FullBridge
