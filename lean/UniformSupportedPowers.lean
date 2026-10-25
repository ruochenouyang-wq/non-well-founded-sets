import UniformHereditarySupport
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop} {swap : Nat → U → U}

/-- Here the actual ambient powerset works, and no trace existence
    hypothesis or commutativity hypothesis is needed. -/
theorem supported_uniform_ambient_powerset (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} (a : SupportedCarrier s swap) (ha : UniformHereditarySupport s swap N a.val) :
    ∃ p : SupportedCarrier s swap,
      UniformHereditarySupport s swap N p.val ∧
      (∀ x, s x p.val ↔ Subset s x a.val) ∧
      (∀ X, supportedMember swap X p ↔ Subset (supportedMember swap) X a) := by
  obtain ⟨p, hp⟩ := base.powerset a.val
  have hu := uniform_support_powerset base hj ho ha hp
  exact ⟨⟨p, uniform_support_hereditary hu⟩, hu, hp,
    fun X => (hp X.val).trans (supported_subset_iff X a).symm⟩

noncomputable def ambientPowerTower (base : BaseCollection s) (a : U) : Nat → U
  | 0 => a
  | n+1 => Classical.choose (base.powerset (ambientPowerTower base a n))

theorem ambient_power_tower_step (base : BaseCollection s) (a : U) (n : Nat) :
    ∀ x, s x (ambientPowerTower base a (n+1)) ↔ Subset s x (ambientPowerTower base a n) :=
  Classical.choose_spec (base.powerset (ambientPowerTower base a n))

/-- This is iteration over external standard natural numbers; it is not
    asserted to be a source-coded function on the entire internal omega. -/
theorem ambient_power_tower_uniform (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} {a : U} (ha : UniformHereditarySupport s swap N a) (k : Nat) :
    UniformHereditarySupport s swap N (ambientPowerTower base a k) := by
  induction k with
  | zero => exact ha
  | succ k ih => exact uniform_support_powerset base hj ho ih (ambient_power_tower_step base a k)

/-- In particular all finite ambient powerset levels above the full
    internal natural-number object are present in the candidate. -/
theorem supported_internal_omega_power_tower (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    (hl : ∀ n, LocallyInternalTransitiveMap s (swap n)) :
    ∃ z w, OmegaCode s z w ∧ ∃ T : Nat → SupportedCarrier s swap,
      (T 0).val = w ∧
      (∀ k, UniformHereditarySupport s swap 0 (T k).val) ∧
      (∀ k x, s x (T (k+1)).val ↔ Subset s x (T k).val) ∧
      (∀ k X, supportedMember swap X (T (k+1)) ↔ Subset (supportedMember swap) X (T k)) := by
  obtain ⟨z, w, hw⟩ := internal_omega_exists base
  have hW := uniform_support_internally_wellFounded base hl
    (internal_omega_transitive base hw) (internal_omega_wellFounded base hw)
  have hT := ambient_power_tower_uniform base hj ho hW
  let T : Nat → SupportedCarrier s swap := fun k =>
    ⟨ambientPowerTower base w k, uniform_support_hereditary (hT k)⟩
  exact ⟨z, w, hw, T, rfl, hT, ambient_power_tower_step base w,
    fun k X => (ambient_power_tower_step base w k X.val).trans (supported_subset_iff X (T k)).symm⟩

#print axioms supported_uniform_ambient_powerset
#print axioms supported_internal_omega_power_tower
end FullBridge
