import JointMaskRelativePower
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem joint_mask_domain_power_tower (base : BaseCollection s) {w t : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t)
    (hj : ∀ a, ElementaryMap s s (J a)) (hs : ∀ a x, J a (J a x) = x) (n : Nat) :
    Nonempty (JointMaskDomain s w J (ambientPowerTower base t n)) := by
  induction n with
  | zero => exact ⟨A⟩
  | succ n ih =>
    obtain ⟨B⟩ := ih
    exact joint_mask_domain_powerset base B hj hs (ambient_power_tower_step base t n)

/-- The ambient domain need not itself be hereditarily supported. -/
structure MaskPowerStage (s : U → U → Prop) (w : U) (J : InternalMask s w → U → U) where
  domain : U
  joint : JointMaskDomain s w J domain
  value : MaskSupportedCarrier s w J
  bounded : Subset s value.val domain

theorem mask_power_stage_successor (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ a, ElementaryMap s s (J a))
    (hc : ∀ a b x, J a (J b x) = J b (J a x)) (hs : ∀ a x, J a (J a x) = x)
    (A : MaskPowerStage s w J) : ∃ B : MaskPowerStage s w J,
      (∀ x, s x B.domain ↔ Subset s x A.domain) ∧
      (∀ L, s L B.value.val ↔ HereditarilyMaskSupported s w J L ∧ Subset s L A.value.val) ∧
      (∀ x, maskSupportedMember J x B.value ↔ Subset (maskSupportedMember J) x A.value) := by
  obtain ⟨q, hq⟩ := base.powerset A.domain
  obtain ⟨Q⟩ := joint_mask_domain_powerset base A.joint hj hs hq
  obtain ⟨p, hp, hrel⟩ := joint_mask_relative_power base A.joint hj hc hs A.value A.bounded
  have hbound : Subset s p.val q := by
    intro L hL
    apply (hq L).mpr
    exact fun x hx => A.bounded x (((hp L).mp hL).2 x hx)
  exact ⟨⟨q, Q, p, hbound⟩, hq, hp, hrel⟩

/-- External Nat iteration with actual source sets and joint codes at every
    stage. No function on the full source-internal omega is asserted. -/
theorem mask_power_stage_sequence (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ a, ElementaryMap s s (J a))
    (hc : ∀ a b x, J a (J b x) = J b (J a x)) (hs : ∀ a x, J a (J a x) = x)
    (A : MaskPowerStage s w J) : ∃ S : Nat → MaskPowerStage s w J, S 0 = A ∧
      (∀ n x, s x (S (n+1)).domain ↔ Subset s x (S n).domain) ∧
      (∀ n L, s L (S (n+1)).value.val ↔ HereditarilyMaskSupported s w J L ∧ Subset s L (S n).value.val) ∧
      (∀ n x, maskSupportedMember J x (S (n+1)).value ↔ Subset (maskSupportedMember J) x (S n).value) := by
  let next : MaskPowerStage s w J → MaskPowerStage s w J :=
    fun B => Classical.choose (mask_power_stage_successor base hj hc hs B)
  let S : Nat → MaskPowerStage s w J := fun n => Nat.rec A (fun _ B => next B) n
  have hnext := fun B => Classical.choose_spec (mask_power_stage_successor base hj hc hs B)
  exact ⟨S, rfl, fun n => (hnext (S n)).1, fun n => (hnext (S n)).2.1,
    fun n => (hnext (S n)).2.2⟩

/-- The newly constructed joint-code power tower belongs to the same actual
    no-choice hereditary candidate. Full model axioms remain separate. -/
theorem countable_bafa_joint_power_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ P : InternalQuinePairs s w, ∃ J : InternalMask s w → U → U,
      (∀ a, ElementaryMap s s (J a) ∧ (∀ y, ∃ x, J a x = y) ∧ LocallyInternalTransitiveMap s (J a)) ∧
      (∀ a b x, J a (J b x) = J b (J a x)) ∧ (∀ a x, J a (J a x) = x) ∧
      (∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x) ∧
      Extensional (maskSupportedMember J) ∧ Empty (maskSupportedMember J) ∧
      Pairing (maskSupportedMember J) ∧ Union (maskSupportedMember J) ∧ Infinity (maskSupportedMember J) ∧
      BoundedSeparation (maskSupportedMember J) ∧ ¬ ChoiceCode (maskSupportedMember J) ∧
      ∃ S : Nat → MaskPowerStage s w J,
        (S 0).domain = (S 0).value.val ∧
        (∀ x, s x (S 0).domain ↔ ∃ c, s c P.family ∧ s x c) ∧
        (∀ n x, s x (S (n+1)).domain ↔ Subset s x (S n).domain) ∧
        (∀ n L, s L (S (n+1)).value.val ↔ HereditarilyMaskSupported s w J L ∧ Subset s L (S n).value.val) ∧
        (∀ n x, maskSupportedMember J x (S (n+1)).value ↔ Subset (maskSupportedMember J) x (S n).value) := by
  obtain ⟨z, w, hw, P, J, hJ, hc, hs, hcore, _, he, hz, hp, hu, hi, hsep, hno, _, d, hd, _⟩ :=
    countable_bafa_mask_supported_candidate base hB enum henum
  obtain ⟨D⟩ := joint_mask_label_domain base P J hcore hd
  let A : MaskPowerStage s w J := ⟨d.val, D, d, fun _ hx => hx⟩
  obtain ⟨S, hS, hdom, htrace, hrel⟩ := mask_power_stage_sequence base (fun a => (hJ a).1) hc hs A
  refine ⟨z, w, hw, P, J, hJ, hc, hs, hcore, he, hz, hp, hu, hi, hsep, hno,
    S, ?_, ?_, hdom, htrace, hrel⟩
  · rw [hS]
  · rw [hS]
    exact hd

#print axioms countable_bafa_joint_power_candidate
#print axioms mask_carrier_power_of_joint_covers
end FullBridge
