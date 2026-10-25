import MaskRelativePower
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem mask_cons_values {w : U} {J : InternalMask s w → U → U} {n}
    (x : MaskSupportedCarrier s w J) (v : Fin n → MaskSupportedCarrier s w J) :
    (fun i => (cons x v i).val) = cons x.val (fun i => (v i).val) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem mask_bounded_absoluteness {w : U} {J : InternalMask s w → U → U} {n} (p : BoundedFormula n)
    (v : Fin n → MaskSupportedCarrier s w J) :
    BoundedEval (maskSupportedMember J) p v ↔ BoundedEval s p (fun i => (v i).val) := by
  induction p with
  | equal i j => exact ⟨congrArg Subtype.val, Subtype.ext⟩
  | member => rfl
  | bottom => rfl
  | conj p q hp hq => exact and_congr (hp v) (hq v)
  | impl p q hp hq => exact imp_congr (hp v) (hq v)
  | exMem i p hp =>
    constructor
    · rintro ⟨x, hx, hpx⟩
      exact ⟨x.val, hx, by simpa only [mask_cons_values] using (hp (cons x v)).mp hpx⟩
    · rintro ⟨x, hx, hpx⟩
      let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member (v i).property hx⟩
      exact ⟨X, hx, (hp (cons X v)).mpr (by simpa only [mask_cons_values] using hpx)⟩
  | allMem i p hp =>
    constructor
    · intro h x hx
      let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member (v i).property hx⟩
      simpa only [mask_cons_values] using (hp (cons X v)).mp (h X hx)
    · intro h x hx
      exact (hp (cons x v)).mpr (by simpa only [mask_cons_values] using h x.val hx)

theorem mask_fixed_finite_parameters (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    {J : InternalMask s w → U → U} {n} (v : Fin n → U)
    (hv : ∀ i, MaskTailSupported s w J (v i)) :
    ∃ N, s N w ∧ ∀ a, (∀ i, s i a.val → ¬s i N) → ∀ i, J a (v i) = v i := by
  induction n with
  | zero => exact ⟨z, hw.2.1.1, fun _ _ i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨M, hM, hm⟩ := hv 0
    obtain ⟨K, hK, hk⟩ := ih (fun i => v i.succ) (fun i => hv i.succ)
    obtain ⟨N, hN, hMN, hKN⟩ := internal_omega_common_bound base hw hM hK
    refine ⟨N, hN, fun a hdis i => ?_⟩
    exact Fin.cases (hm a (fun j hj h => hdis j hj (hMN j h)))
      (fun k => hk a (fun j hj h => hdis j hj (hKN j h)) k) i

theorem hereditary_mask_source_separation (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    {J : InternalMask s w → U → U} (hj : ∀ a, ElementaryMap s s (J a))
    (ho : ∀ a y, ∃ x, J a x = y) {n} (p : Formula (n+1)) (v : Fin n → U) {x b : U}
    (hx : HereditarilyMaskSupported s w J x) (hv : ∀ i, HereditarilyMaskSupported s w J (v i))
    (hb : ∀ y, s y b ↔ s y x ∧ Eval s p (cons y v)) : HereditarilyMaskSupported s w J b := by
  apply hereditary_mask_intro
  · obtain ⟨M, hM, hm⟩ := hereditary_mask_root hx
    obtain ⟨K, hK, hk⟩ := mask_fixed_finite_parameters base hw v (fun i => hereditary_mask_root (hv i))
    obtain ⟨N, hN, hMN, hKN⟩ := internal_omega_common_bound base hw hM hK
    exact ⟨N, hN, fun a hdis => elementary_map_separation_set base (hj a) (ho a) p v hb
      (hm a (fun i hi h => hdis i hi (hMN i h)))
      (hk a (fun i hi h => hdis i hi (hKN i h)))⟩
  · exact fun y hy => hereditary_mask_member hx ((hb y).mp hy).1

theorem mask_carrier_bounded_separation (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    (J : InternalMask s w → U → U) (hj : ∀ a, ElementaryMap s s (J a))
    (ho : ∀ a y, ∃ x, J a x = y) : BoundedSeparation (maskSupportedMember J) := by
  intro n p v a
  obtain ⟨b, hb⟩ := base.separation n p.toFormula (fun i => (v i).val) a.val
  have hB := hereditary_mask_source_separation base hw hj ho p.toFormula (fun i => (v i).val)
    a.property (fun i => (v i).property) hb
  refine ⟨⟨b, hB⟩, fun x => ?_⟩
  have hsem := (bounded_eval_toFormula (s := s) p (cons x.val (fun i => (v i).val))).trans
    (by simpa only [mask_cons_values] using (mask_bounded_absoluteness p (cons x v)).symm)
  exact (hb x.val).trans (and_congr Iff.rfl hsem)

theorem hereditary_mask_internally_wellFounded (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hl : ∀ a, LocallyInternalTransitiveMap s (J a)) {t : U}
    (ht : TransitiveCode s t) (hwt : InternallyWellFounded s t) : HereditarilyMaskSupported s w J t := by
  have hq : ∀ a x, internalCode base (J a x) = internalCode base x := fun a x =>
    (internal_code_eq base _ _).mpr (locally_internal_map_behavior base _ (hl a) x)
  intro y hy
  cases hy with
  | refl =>
    exact ⟨z, hw.2.1.1, fun a _ => ((internally_wellFounded_root_fiber base ht hwt).mp (hq a t).symm).symm⟩
  | step hzt hzy =>
    have hyt := descendant_in_transitive ht hzt hzy
    exact ⟨z, hw.2.1.1, fun a _ => ((internally_wellFounded_member_fiber base ht hwt hyt).mp (hq a y).symm).symm⟩

theorem mask_carrier_infinity (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    (J : InternalMask s w → U → U) (hl : ∀ a, LocallyInternalTransitiveMap s (J a)) :
    Infinity (maskSupportedMember J) := by
  have hW := hereditary_mask_internally_wellFounded base hw hl (internal_omega_transitive base hw)
    (internal_omega_wellFounded base hw)
  let W : MaskSupportedCarrier s w J := ⟨w, hW⟩
  let Z : MaskSupportedCarrier s w J := ⟨z, hereditary_mask_member hW hw.2.1.1⟩
  refine ⟨W, ⟨Z, hw.2.1.1, fun x hx => hw.1 x.val hx⟩, ?_⟩
  intro x hx
  obtain ⟨y, hxy⟩ := successor_exists base x.val
  have hyw := hw.2.1.2 x.val hx y hxy
  let Y : MaskSupportedCarrier s w J := ⟨y, hereditary_mask_member hW hyw⟩
  refine ⟨Y, hyw, fun t => ?_⟩
  exact (hxy t.val).trans (or_congr Iff.rfl ⟨Subtype.ext, congrArg Subtype.val⟩)
end FullBridge
