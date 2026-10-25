import InternalMaskBounds
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def HereditarilyMaskSupported (s : U → U → Prop) (w : U)
    (J : InternalMask s w → U → U) (x : U) : Prop :=
  ∀ y, MemberDescendant s x y → MaskTailSupported s w J y

def MaskSupportedCarrier (s : U → U → Prop) (w : U) (J : InternalMask s w → U → U) :=
  {x : U // HereditarilyMaskSupported s w J x}

def maskSupportedMember {w : U} (J : InternalMask s w → U → U)
    (x y : MaskSupportedCarrier s w J) : Prop := s x.val y.val

theorem hereditary_mask_root {w : U} {J : InternalMask s w → U → U} {x : U}
    (hx : HereditarilyMaskSupported s w J x) : MaskTailSupported s w J x := hx x (.refl x)

theorem hereditary_mask_member {w : U} {J : InternalMask s w → U → U} {x y : U}
    (hx : HereditarilyMaskSupported s w J x) (hy : s y x) : HereditarilyMaskSupported s w J y :=
  fun z hz => hx z (.step hy hz)

theorem hereditary_mask_intro {w : U} {J : InternalMask s w → U → U} {x : U}
    (hx : MaskTailSupported s w J x)
    (hm : ∀ y, s y x → HereditarilyMaskSupported s w J y) : HereditarilyMaskSupported s w J x := by
  intro y hy
  cases hy with
  | refl => exact hx
  | step hz hzy => exact hm _ hz _ hzy

theorem hereditary_mask_quine {w : U} {J : InternalMask s w → U → U} {x : U}
    (hq : SelfSingleton s x) (hx : MaskTailSupported s w J x) : HereditarilyMaskSupported s w J x := by
  intro y hy
  have he : y = x := by
    induction hy with
    | refl => rfl
    | @step x z y hxz hzy ih =>
      have hzx := (hq z).mp hxz
      subst z
      exact ih hq hx
  exact he.symm ▸ hx

theorem mask_support_invariant {w : U} {J : InternalMask s w → U → U}
    (hc : ∀ a b x, J a (J b x) = J b (J a x))
    (hs : ∀ a x, J a (J a x) = x) (a : InternalMask s w) (x : U) :
    MaskTailSupported s w J (J a x) ↔ MaskTailSupported s w J x := by
  have hf : ∀ {x}, MaskTailSupported s w J x → MaskTailSupported s w J (J a x) := by
    rintro x ⟨N, hN, hfix⟩
    exact ⟨N, hN, fun b hb => (hc b a x).trans (congrArg (J a) (hfix b hb))⟩
  exact ⟨fun h => hs a x ▸ hf h, fun h => hf h⟩

theorem hereditary_mask_invariant {w : U} {J : InternalMask s w → U → U}
    (hj : ∀ a, ElementaryMap s s (J a))
    (hc : ∀ a b x, J a (J b x) = J b (J a x))
    (hs : ∀ a x, J a (J a x) = x) (a : InternalMask s w) (x : U) :
    HereditarilyMaskSupported s w J (J a x) ↔ HereditarilyMaskSupported s w J x := by
  have hf : ∀ {x}, HereditarilyMaskSupported s w J x → HereditarilyMaskSupported s w J (J a x) := by
    intro x hx y hy
    have hm : ∀ u v, s u v → s (J a u) (J a v) := fun u v h =>
      ((hj a) (Formula.member (n := 2) 0 1) (cons u (cons v Fin.elim0))).mp h
    have hdesc := member_descendant_map hm hy
    rw [hs a x] at hdesc
    exact (mask_support_invariant hc hs a y).mp (hx (J a y) hdesc)
  exact ⟨fun h => hs a x ▸ hf h, fun h => hf h⟩

theorem mask_carrier_extensional (he : Extensional s) {w : U} (J : InternalMask s w → U → U) :
    Extensional (maskSupportedMember J) := by
  intro a b hab
  apply Subtype.ext
  apply he
  intro x
  constructor
  · intro hx
    exact (hab ⟨x, hereditary_mask_member a.property hx⟩).mp hx
  · intro hx
    exact (hab ⟨x, hereditary_mask_member b.property hx⟩).mpr hx

theorem hereditary_mask_empty (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    (J : InternalMask s w → U → U) (hj : ∀ a, ElementaryMap s s (J a))
    (ho : ∀ a y, ∃ x, J a x = y) {e : U} (he : IsEmpty s e) : HereditarilyMaskSupported s w J e := by
  apply hereditary_mask_intro
  · exact ⟨z, hw.2.1.1, fun a _ => elementary_map_fixed_members_set base (hj a) (ho a)
      (fun x hx => False.elim (he x hx))⟩
  · exact fun x hx => False.elim (he x hx)

theorem hereditary_mask_pair (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    {J : InternalMask s w → U → U} (hj : ∀ a, ElementaryMap s s (J a)) {x y p : U}
    (hx : HereditarilyMaskSupported s w J x) (hy : HereditarilyMaskSupported s w J y)
    (hp : IsPair s p x y) : HereditarilyMaskSupported s w J p := by
  apply hereditary_mask_intro
  · obtain ⟨N, hN, hfix⟩ := mask_support_common_bound base hw (hereditary_mask_root hx) (hereditary_mask_root hy)
    refine ⟨N, hN, fun a ha => ?_⟩
    have hh := elementary_map_pair (hj a) hp
    rw [(hfix a ha).1, (hfix a ha).2] at hh
    exact pair_unique base.extensional hh hp
  · intro t ht
    exact ((hp t).mp ht).elim (fun h => h ▸ hx) (fun h => h ▸ hy)

theorem hereditary_mask_union (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ a, ElementaryMap s s (J a))
    (ho : ∀ a y, ∃ x, J a x = y) {x d : U}
    (hx : HereditarilyMaskSupported s w J x) (hd : ∀ t, s t d ↔ ∃ y, s y x ∧ s t y) :
    HereditarilyMaskSupported s w J d := by
  apply hereditary_mask_intro
  · obtain ⟨N, hN, hfix⟩ := hereditary_mask_root hx
    exact ⟨N, hN, fun a ha => elementary_map_union_set base (hj a) (ho a) hd (hfix a ha)⟩
  · intro t ht
    obtain ⟨y, hy, hty⟩ := (hd t).mp ht
    exact hereditary_mask_member (hereditary_mask_member hx hy) hty

theorem mask_carrier_empty (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    (J : InternalMask s w → U → U) (hj : ∀ a, ElementaryMap s s (J a))
    (ho : ∀ a y, ∃ x, J a x = y) : Empty (maskSupportedMember J) := by
  obtain ⟨e, he⟩ := base.empty
  exact ⟨⟨e, hereditary_mask_empty base hw J hj ho he⟩, fun x hx => he x.val hx⟩

theorem mask_carrier_pairing (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    (J : InternalMask s w → U → U) (hj : ∀ a, ElementaryMap s s (J a)) : Pairing (maskSupportedMember J) := by
  intro a b
  obtain ⟨c, hc⟩ := base.pairing a.val b.val
  refine ⟨⟨c, hereditary_mask_pair base hw hj a.property b.property hc⟩, fun x => ?_⟩
  exact (hc x.val).trans (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)

theorem mask_carrier_union (base : BaseCollection s) {w : U}
    (J : InternalMask s w → U → U) (hj : ∀ a, ElementaryMap s s (J a))
    (ho : ∀ a y, ∃ x, J a x = y) : Union (maskSupportedMember J) := by
  intro a
  obtain ⟨b, hb⟩ := base.union a.val
  refine ⟨⟨b, hereditary_mask_union base hj ho a.property hb⟩, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (hb x.val).mp hx
    exact ⟨⟨y, hereditary_mask_member a.property hy⟩, hy, hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact (hb x.val).mpr ⟨y.val, hy, hxy⟩

theorem mask_carrier_subset_iff {w : U} {J : InternalMask s w → U → U}
    (x a : MaskSupportedCarrier s w J) : Subset (maskSupportedMember J) x a ↔ Subset s x.val a.val := by
  constructor
  · intro h y hy
    exact h ⟨y, hereditary_mask_member x.property hy⟩ hy
  · intro h y hy
    exact h y.val hy
end FullBridge
