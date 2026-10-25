import UniformSupportedChoice
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop} {swap : Nat → U → U}

/-- Only immediate members share a bound. Deeper descendants may have
    different, unbounded support bounds. -/
def FixedMembersAfter (s : U → U → Prop) (swap : Nat → U → U) (N : Nat) (a : U) : Prop :=
  ∀ x, s x a → ∀ n, N ≤ n → swap n x = x

theorem supported_subset_of_fixed_members (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} {a b : U} (ha : HereditarilyEventuallyFixed s swap a)
    (hm : FixedMembersAfter s swap N a) (hb : Subset s b a) :
    (∀ n, N ≤ n → swap n b = b) ∧ HereditarilyEventuallyFixed s swap b := by
  have hr : ∀ n, N ≤ n → swap n b = b := fun n hn =>
    elementary_map_fixed_members_set base (hj n) (ho n) (fun x hx => hm x (hb x hx) n hn)
  exact ⟨hr, hereditary_support_intro ⟨N, hr⟩
    (fun x hx => hereditary_support_member ha (hb x hx))⟩

theorem supported_powerset_of_fixed_members (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} {a p : U} (ha : HereditarilyEventuallyFixed s swap a)
    (hm : FixedMembersAfter s swap N a) (hp : ∀ x, s x p ↔ Subset s x a) :
    HereditarilyEventuallyFixed s swap p ∧ FixedMembersAfter s swap N p := by
  have hs := fun x hx => supported_subset_of_fixed_members base hj ho ha hm ((hp x).mp hx)
  have hpm : FixedMembersAfter s swap N p := fun x hx => (hs x hx).1
  exact ⟨hereditary_support_intro
    ⟨N, fun n hn => elementary_map_fixed_members_set base (hj n) (ho n) (fun x hx => hpm x hx n hn)⟩
    (fun x hx => (hs x hx).2), hpm⟩

theorem supported_fixed_members_power_tower (base : BaseCollection s)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y)
    {N : Nat} {a : U} (ha : HereditarilyEventuallyFixed s swap a)
    (hm : FixedMembersAfter s swap N a) (k : Nat) :
    HereditarilyEventuallyFixed s swap (ambientPowerTower base a k) ∧
      FixedMembersAfter s swap N (ambientPowerTower base a k) := by
  induction k with
  | zero => exact ⟨ha, hm⟩
  | succ k ih =>
    exact supported_powerset_of_fixed_members base hj ho ih.1 ih.2 (ambient_power_tower_step base a k)

/-- The no-choice family itself retains every finite ambient powerset
    level, despite lacking a uniform hereditary support bound. -/
theorem pair_sequence_family_power_tower (base : BaseCollection s) {F : U}
    (S : PairSwapSequence s F) :
    ∃ T : Nat → SupportedCarrier s S.map, (T 0).val = F ∧
      (∀ k, FixedMembersAfter s S.map 0 (T k).val) ∧
      (∀ k x, s x (T (k+1)).val ↔ Subset s x (T k).val) ∧
      (∀ k X, supportedMember S.map X (T (k+1)) ↔ Subset (supportedMember S.map) X (T k)) := by
  have hF := pair_sequence_family_hereditarily_supported S
  have hm : FixedMembersAfter s S.map 0 F := fun c hc n _ => (S.action n).fix_rows c hc
  have hT := supported_fixed_members_power_tower base (fun n => (S.action n).elementary)
    (fun n => (S.action n).onto) hF hm
  let T : Nat → SupportedCarrier s S.map := fun k => ⟨ambientPowerTower base F k, (hT k).1⟩
  exact ⟨T, rfl, fun k => (hT k).2, ambient_power_tower_step base F,
    fun k X => (ambient_power_tower_step base F k X.val).trans (supported_subset_iff X (T k)).symm⟩

/-- One concrete candidate simultaneously retains all source powerset
    levels above F and excludes the source powerset of the union of F.
    Exclusion still does not refute its own relative PowerSet axiom. -/
theorem countable_bafa_supported_power_contrast (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ F, ∃ S : PairSwapSequence s F,
      (∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) ∧
      HereditarilyEventuallyFixed s S.map F ∧
      (¬ ∃ N, UniformHereditarySupport s S.map N F) ∧
      ¬ ChoiceCode (supportedMember (s := s) S.map) ∧
      (∃ T : Nat → SupportedCarrier s S.map, (T 0).val = F ∧
        (∀ k, FixedMembersAfter s S.map 0 (T k).val) ∧
        (∀ k x, s x (T (k+1)).val ↔ Subset s x (T k).val) ∧
        (∀ k X, supportedMember S.map X (T (k+1)) ↔ Subset (supportedMember S.map) X (T k))) ∧
      (∃ d p, HereditarilyEventuallyFixed s S.map d ∧
        (∀ y, s y d ↔ ∃ c, s c F ∧ s y c) ∧
        (∀ x, s x p ↔ Subset s x d) ∧ ¬ HereditarilyEventuallyFixed s S.map p) := by
  obtain ⟨F, S, f, hf⟩ := bafa_pair_sequence_with_ambient_choice base hB enum henum
  obtain ⟨T, _, _, hc⟩ := pair_sequence_commuting_extension base hB enum henum S
  obtain ⟨d, L, hd, hdu, _, hLd, hnL⟩ := pair_sequence_choice_range_excluded base T hf
  obtain ⟨p, hp⟩ := base.powerset d
  refine ⟨F, T, hc, pair_sequence_family_hereditarily_supported T,
    pair_sequence_family_not_uniform T, pair_sequence_supported_carrier_not_choice T,
    pair_sequence_family_power_tower base T, d, p, hd, hdu, hp, ?_⟩
  intro hP
  exact hnL (hereditary_support_member hP ((hp L).mpr hLd))

#print axioms pair_sequence_family_power_tower
#print axioms countable_bafa_supported_power_contrast
end FullBridge
