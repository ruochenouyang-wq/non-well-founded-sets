import SupportedTruthGap
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop} {swap : Nat → U → U}

/-- One bound for every finite membership descendant, not one bound per
    descendant. This is strictly stronger than hereditary eventual fixing. -/
def UniformHereditarySupport (s : U → U → Prop) (swap : Nat → U → U) (N : Nat) (a : U) : Prop :=
  ∀ x, MemberDescendant s a x → ∀ n, N ≤ n → swap n x = x

theorem uniform_support_root {N : Nat} {a : U}
    (ha : UniformHereditarySupport s swap N a) : ∀ n, N ≤ n → swap n a = a :=
  ha a (.refl a)

theorem uniform_support_member {N : Nat} {a x : U}
    (ha : UniformHereditarySupport s swap N a) (hx : s x a) :
    UniformHereditarySupport s swap N x := fun y hy => ha y (.step hx hy)

theorem uniform_support_hereditary {N : Nat} {a : U}
    (ha : UniformHereditarySupport s swap N a) : HereditarilyEventuallyFixed s swap a :=
  fun x hx => ⟨N, ha x hx⟩

theorem uniform_support_mono {N M : Nat} (hNM : N ≤ M) {a : U}
    (ha : UniformHereditarySupport s swap N a) : UniformHereditarySupport s swap M a :=
  fun x hx n hn => ha x hx n (Nat.le_trans hNM hn)

theorem uniform_support_intro {N : Nat} {a : U}
    (hr : ∀ n, N ≤ n → swap n a = a)
    (hm : ∀ x, s x a → UniformHereditarySupport s swap N x) :
    UniformHereditarySupport s swap N a := by
  intro x hx
  cases hx with
  | refl => exact hr
  | step hy hyx => exact hm _ hy _ hyx

/-- Extensionality and surjectivity fix a set whenever all its members
    are fixed. A common bound consequently also fixes every descendant. -/
theorem uniform_support_of_members (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} {a : U} (hm : ∀ x, s x a → UniformHereditarySupport s swap N x) :
    UniformHereditarySupport s swap N a := by
  apply uniform_support_intro
  · intro n hn
    exact elementary_map_fixed_members_set base (hj n) (ho n)
      (fun x hx => uniform_support_root (hm x hx) n hn)
  · exact hm

theorem uniform_support_subset (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} {a b : U} (ha : UniformHereditarySupport s swap N a) (hb : Subset s b a) :
    UniformHereditarySupport s swap N b :=
  uniform_support_of_members base hj ho (fun x hx => uniform_support_member ha (hb x hx))

theorem uniform_support_pair (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} {a b p : U} (ha : UniformHereditarySupport s swap N a)
    (hb : UniformHereditarySupport s swap N b) (hp : IsPair s p a b) :
    UniformHereditarySupport s swap N p := by
  apply uniform_support_of_members base hj ho
  intro x hx
  exact ((hp x).mp hx).elim (fun h => h ▸ ha) (fun h => h ▸ hb)

theorem uniform_support_union (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} {a b : U} (ha : UniformHereditarySupport s swap N a)
    (hb : ∀ x, s x b ↔ ∃ y, s y a ∧ s x y) : UniformHereditarySupport s swap N b := by
  apply uniform_support_of_members base hj ho
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (hb x).mp hx
  exact uniform_support_member (uniform_support_member ha hy) hxy

theorem uniform_support_powerset (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} {a p : U} (ha : UniformHereditarySupport s swap N a)
    (hp : ∀ x, s x p ↔ Subset s x a) : UniformHereditarySupport s swap N p :=
  uniform_support_of_members base hj ho
    (fun x hx => uniform_support_subset base hj ho ha ((hp x).mp hx))

theorem uniform_support_internally_wellFounded (base : BaseCollection s)
    (hl : ∀ n, LocallyInternalTransitiveMap s (swap n)) {t : U}
    (ht : TransitiveCode s t) (hw : InternallyWellFounded s t) :
    UniformHereditarySupport s swap 0 t := by
  have hq : ∀ n x, internalCode base (swap n x) = internalCode base x := fun n x =>
    (internal_code_eq base _ _).mpr (locally_internal_map_behavior base _ (hl n) x)
  intro y hy n _
  cases hy with
  | refl => exact ((internally_wellFounded_root_fiber base ht hw).mp (hq n t).symm).symm
  | step hzt hzy =>
    exact ((internally_wellFounded_member_fiber base ht hw
      (descendant_in_transitive ht hzt hzy)).mp (hq n y).symm).symm

#print axioms uniform_support_powerset
#print axioms uniform_support_internally_wellFounded
end FullBridge
