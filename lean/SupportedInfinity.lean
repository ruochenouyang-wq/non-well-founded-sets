import SupportedPairCandidate
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem descendant_in_transitive {t x y : U} (ht : TransitiveCode s t)
    (hx : s x t) (hxy : MemberDescendant s x y) : s y t := by
  induction hxy with
  | refl => exact hx
  | @step x z y hxz hzy ih => exact ih (ht x hx z hxz)

theorem hereditary_support_internally_wellFounded (base : BaseCollection s) {swap : Nat → U → U}
    (hl : ∀ n, LocallyInternalTransitiveMap s (swap n)) {t : U}
    (ht : TransitiveCode s t) (hw : InternallyWellFounded s t) : HereditarilyEventuallyFixed s swap t := by
  have hq : ∀ n x, internalCode base (swap n x) = internalCode base x := fun n x =>
    (internal_code_eq base _ _).mpr (locally_internal_map_behavior base _ (hl n) x)
  intro y hy
  cases hy with
  | refl =>
    exact ⟨0, fun n _ => ((internally_wellFounded_root_fiber base ht hw).mp (hq n t).symm).symm⟩
  | step hzt hzy =>
    have hyt := descendant_in_transitive ht hzt hzy
    exact ⟨0, fun n _ => ((internally_wellFounded_member_fiber base ht hw hyt).mp (hq n y).symm).symm⟩

theorem supported_carrier_infinity (base : BaseCollection s) (swap : Nat → U → U)
    (hl : ∀ n, LocallyInternalTransitiveMap s (swap n)) : Infinity (supportedMember (s := s) swap) := by
  obtain ⟨z, w, hw⟩ := internal_omega_exists base
  have hW := hereditary_support_internally_wellFounded base hl (internal_omega_transitive base hw)
    (internal_omega_wellFounded base hw)
  let W : SupportedCarrier s swap := ⟨w, hW⟩
  let Z : SupportedCarrier s swap := ⟨z, hereditary_support_member hW hw.2.1.1⟩
  refine ⟨W, ⟨Z, hw.2.1.1, fun x hx => hw.1 x.val hx⟩, ?_⟩
  intro x hx
  obtain ⟨y, hxy⟩ := successor_exists base x.val
  have hyw := hw.2.1.2 x.val hx y hxy
  let Y : SupportedCarrier s swap := ⟨y, hereditary_support_member hW hyw⟩
  refine ⟨Y, hyw, fun t => ?_⟩
  exact (hxy t.val).trans (or_congr Iff.rfl ⟨Subtype.ext, congrArg Subtype.val⟩)

/-- Strengthens the actual no-choice candidate with Infinity. No PowerSet,
    Separation, Collection or BAFA assertion is bundled into this theorem. -/
theorem countable_bafa_supported_infinite_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ F, ∃ S : PairSwapSequence s F,
      HereditarilyEventuallyFixed s S.map F ∧
      Extensional (supportedMember (s := s) S.map) ∧ Empty (supportedMember (s := s) S.map) ∧
      Pairing (supportedMember (s := s) S.map) ∧ Union (supportedMember (s := s) S.map) ∧
      Infinity (supportedMember (s := s) S.map) ∧ ¬ ChoiceCode (supportedMember (s := s) S.map) := by
  obtain ⟨F, S, hF, he, hz, hp, hu, hn⟩ := countable_bafa_supported_pair_candidate base hB enum henum
  exact ⟨F, S, hF, he, hz, hp, hu, supported_carrier_infinity base S.map
    (fun n => (S.action n).locally_internal), hn⟩

#print axioms countable_bafa_supported_infinite_candidate
end FullBridge
