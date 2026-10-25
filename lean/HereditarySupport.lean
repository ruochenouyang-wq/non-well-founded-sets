import InternalPairSwaps
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

inductive MemberDescendant (s : U → U → Prop) : U → U → Prop
  | refl (x : U) : MemberDescendant s x x
  | step {x y z : U} : s y x → MemberDescendant s y z → MemberDescendant s x z

def EventuallyFixedBy (swap : Nat → U → U) (x : U) : Prop :=
  ∃ N, ∀ n, N ≤ n → swap n x = x

def HereditarilyEventuallyFixed (s : U → U → Prop) (swap : Nat → U → U) (x : U) : Prop :=
  ∀ y, MemberDescendant s x y → EventuallyFixedBy swap y

def SupportedCarrier (s : U → U → Prop) (swap : Nat → U → U) :=
  {x : U // HereditarilyEventuallyFixed s swap x}

def supportedMember (swap : Nat → U → U) (x y : SupportedCarrier s swap) : Prop := s x.val y.val

theorem hereditary_support_root {swap : Nat → U → U} {x : U}
    (hx : HereditarilyEventuallyFixed s swap x) : EventuallyFixedBy swap x := hx x (.refl x)

theorem hereditary_support_member {swap : Nat → U → U} {x y : U}
    (hx : HereditarilyEventuallyFixed s swap x) (hy : s y x) : HereditarilyEventuallyFixed s swap y :=
  fun z hz => hx z (.step hy hz)

theorem hereditary_support_intro {swap : Nat → U → U} {x : U}
    (hx : EventuallyFixedBy swap x)
    (hm : ∀ y, s y x → HereditarilyEventuallyFixed s swap y) : HereditarilyEventuallyFixed s swap x := by
  intro y hy
  cases hy with
  | refl => exact hx
  | step hz hzy => exact hm _ hz _ hzy

theorem hereditary_support_quine {swap : Nat → U → U} {x : U}
    (hq : SelfSingleton s x) (hx : EventuallyFixedBy swap x) : HereditarilyEventuallyFixed s swap x := by
  intro y hy
  have he : y = x := by
    induction hy with
    | refl => rfl
    | @step x z y hxz hzy ih =>
      have hzx := (hq z).mp hxz
      subst z
      exact ih hq hx
  exact he.symm ▸ hx

theorem supported_carrier_extensional (he : Extensional s) (swap : Nat → U → U) :
    Extensional (supportedMember (s := s) swap) := by
  intro a b hab
  apply Subtype.ext
  apply he
  intro x
  constructor
  · intro hx
    exact (hab ⟨x, hereditary_support_member a.property hx⟩).mp hx
  · intro hx
    exact (hab ⟨x, hereditary_support_member b.property hx⟩).mpr hx

theorem hereditary_support_empty (base : BaseCollection s) (swap : Nat → U → U)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y) {e : U}
    (he : IsEmpty s e) : HereditarilyEventuallyFixed s swap e := by
  apply hereditary_support_intro
  · refine ⟨0, fun n _ => ?_⟩
    exact elementary_map_fixed_members_set base (hj n) (ho n) (fun x hx => False.elim (he x hx))
  · exact fun x hx => False.elim (he x hx)

theorem hereditary_support_pair (base : BaseCollection s) {swap : Nat → U → U}
    (hj : ∀ n, ElementaryMap s s (swap n)) {a b c : U}
    (ha : HereditarilyEventuallyFixed s swap a) (hb : HereditarilyEventuallyFixed s swap b)
    (hc : IsPair s c a b) : HereditarilyEventuallyFixed s swap c := by
  apply hereditary_support_intro
  · obtain ⟨N, hN⟩ := hereditary_support_root ha
    obtain ⟨M, hM⟩ := hereditary_support_root hb
    refine ⟨max N M, fun n hn => ?_⟩
    have hh := elementary_map_pair (hj n) hc
    rw [hN n (Nat.le_trans (Nat.le_max_left N M) hn), hM n (Nat.le_trans (Nat.le_max_right N M) hn)] at hh
    exact pair_unique base.extensional hh hc
  · intro x hx
    exact ((hc x).mp hx).elim (fun h => h ▸ ha) (fun h => h ▸ hb)

theorem elementary_map_union_set (base : BaseCollection s) {j : U → U}
    (hj : ElementaryMap s s j) (ho : ∀ y, ∃ x, j x = y) {a b : U}
    (hb : ∀ x, s x b ↔ ∃ y, s y a ∧ s x y) (ha : j a = a) : j b = b := by
  have hm : ∀ x y, s x y ↔ s (j x) (j y) := fun x y => by
    exact hj (Formula.member (n := 2) 0 1) (cons x (cons y Fin.elim0))
  apply base.extensional
  intro z
  obtain ⟨x, rfl⟩ := ho z
  rw [← hm x b, hb x, hb (j x)]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨j y, ha ▸ (hm y a).mp hy, (hm x y).mp hxy⟩
  · rintro ⟨Y, hY, hxY⟩
    obtain ⟨y, rfl⟩ := ho Y
    exact ⟨y, (hm y a).mpr (ha.symm ▸ hY), (hm x y).mpr hxY⟩

theorem hereditary_support_union (base : BaseCollection s) {swap : Nat → U → U}
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y) {a b : U}
    (ha : HereditarilyEventuallyFixed s swap a) (hb : ∀ x, s x b ↔ ∃ y, s y a ∧ s x y) :
    HereditarilyEventuallyFixed s swap b := by
  apply hereditary_support_intro
  · obtain ⟨N, hN⟩ := hereditary_support_root ha
    exact ⟨N, fun n hn => elementary_map_union_set base (hj n) (ho n) hb (hN n hn)⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := (hb x).mp hx
    exact hereditary_support_member (hereditary_support_member ha hy) hxy

theorem supported_carrier_empty (base : BaseCollection s) (swap : Nat → U → U)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y) :
    Empty (supportedMember (s := s) swap) := by
  obtain ⟨e, he⟩ := base.empty
  exact ⟨⟨e, hereditary_support_empty base swap hj ho he⟩, fun x hx => he x.val hx⟩

theorem supported_carrier_pairing (base : BaseCollection s) (swap : Nat → U → U)
    (hj : ∀ n, ElementaryMap s s (swap n)) : Pairing (supportedMember (s := s) swap) := by
  intro a b
  obtain ⟨c, hc⟩ := base.pairing a.val b.val
  refine ⟨⟨c, hereditary_support_pair base hj a.property b.property hc⟩, fun x => ?_⟩
  exact (hc x.val).trans (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)

theorem supported_carrier_union (base : BaseCollection s) (swap : Nat → U → U)
    (hj : ∀ n, ElementaryMap s s (swap n)) (ho : ∀ n y, ∃ x, swap n x = y) :
    Union (supportedMember (s := s) swap) := by
  intro a
  obtain ⟨b, hb⟩ := base.union a.val
  refine ⟨⟨b, hereditary_support_union base hj ho a.property hb⟩, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (hb x.val).mp hx
    exact ⟨⟨y, hereditary_support_member a.property hy⟩, hy, hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact (hb x.val).mpr ⟨y.val, hy, hxy⟩

#print axioms supported_carrier_union
end FullBridge
