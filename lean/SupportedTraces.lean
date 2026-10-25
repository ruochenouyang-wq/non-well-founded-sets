import SupportedInvariance
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- An ambient set representing exactly a predicate on the hereditary carrier.
    Existence is deliberately not included in the definition. -/
def SupportedTrace (swap : Nat → U → U) (P : SupportedCarrier s swap → Prop) (b : U) : Prop :=
  ∀ x, s x b ↔ ∃ X : SupportedCarrier s swap, X.val = x ∧ P X

theorem supported_trace_unique (he : Extensional s) {swap : Nat → U → U}
    {P : SupportedCarrier s swap → Prop} {a b : U}
    (ha : SupportedTrace swap P a) (hb : SupportedTrace swap P b) : a = b :=
  he a b (fun x => (ha x).trans (hb x).symm)

theorem supported_lift_invariant {F : U} (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x))
    (n : Nat) (P : SupportedCarrier s S.map → Prop)
    (hP : ∀ X, P (restrictedPairSwap S hc n X) ↔ P X) (x : U) :
    (∃ X : SupportedCarrier s S.map, X.val = S.map n x ∧ P X) ↔
      (∃ X : SupportedCarrier s S.map, X.val = x ∧ P X) := by
  constructor
  · rintro ⟨X, hX, hp⟩
    refine ⟨restrictedPairSwap S hc n X, ?_, (hP X).mpr hp⟩
    exact (congrArg (S.map n) hX).trans ((S.action n).involutive x)
  · rintro ⟨X, hX, hp⟩
    exact ⟨restrictedPairSwap S hc n X, congrArg (S.map n) hX, (hP X).mpr hp⟩

/-- Symmetry supplies hereditary support once the ambient trace exists.
    It supplies no comprehension principle for constructing the trace. -/
theorem supported_trace_hereditary (base : BaseCollection s) {F : U}
    (S : PairSwapSequence s F)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x))
    {P : SupportedCarrier s S.map → Prop} {b : U} (hb : SupportedTrace S.map P b)
    (hP : ∃ N, ∀ n, N ≤ n → ∀ X, P (restrictedPairSwap S hc n X) ↔ P X) :
    HereditarilyEventuallyFixed s S.map b := by
  apply hereditary_support_intro
  · obtain ⟨N, hN⟩ := hP
    refine ⟨N, fun n hn => ?_⟩
    apply base.extensional
    intro y
    obtain ⟨x, rfl⟩ := (S.action n).onto y
    have hm : s x b ↔ s (S.map n x) (S.map n b) :=
      (S.action n).elementary (Formula.member (n := 2) 0 1) (cons x (cons b Fin.elim0))
    change s (S.map n x) (S.map n b) ↔ s (S.map n x) b
    rw [← hm, hb x, hb (S.map n x)]
    exact (supported_lift_invariant S hc n P (hN n hn) x).symm
  · intro x hx
    obtain ⟨X, hX, _⟩ := (hb x).mp hx
    exact hX ▸ X.property

theorem supported_trace_member {swap : Nat → U → U}
    {P : SupportedCarrier s swap → Prop} {b : U} (hb : SupportedTrace swap P b)
    (X : SupportedCarrier s swap) : s X.val b ↔ P X := by
  constructor
  · intro h
    obtain ⟨Y, hY, hp⟩ := (hb X.val).mp h
    exact (Subtype.ext hY : Y = X) ▸ hp
  · intro hp
    exact (hb X.val).mpr ⟨X, rfl, hp⟩

#print axioms supported_trace_hereditary
end FullBridge
