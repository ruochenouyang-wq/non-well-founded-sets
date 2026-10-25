import BooleanGroupExhaustion
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Elements are actual source subsets, not arbitrary external subsets. -/
abbrev InternalMask (s : U → U → Prop) (w : U) := {a : U // Subset s a w}

theorem internal_mask_ext (base : BaseCollection s) {w : U} {a b : InternalMask s w}
    (h : ∀ x, s x a.val ↔ s x b.val) : a = b := Subtype.ext (base.extensional a.val b.val h)

noncomputable def internalMaskOne (base : BaseCollection s) (w : U) : InternalMask s w :=
  ⟨Classical.choose base.empty, fun x hx => False.elim (Classical.choose_spec base.empty x hx)⟩

theorem internal_mask_one_mem (base : BaseCollection s) (w x : U) :
    ¬s x (internalMaskOne base w).val := Classical.choose_spec base.empty x

theorem internal_mask_xor_exists (base : BaseCollection s) {w : U} (a b : InternalMask s w) :
    ∃ c : InternalMask s w, ∀ x, s x c.val ↔
      (s x a.val ∧ ¬s x b.val) ∨ (s x b.val ∧ ¬s x a.val) := by
  let phi : Formula 3 := (Formula.conj (.member 0 1) (.impl (.member 0 2) .bottom)).disj
    (.conj (.member 0 2) (.impl (.member 0 1) .bottom))
  obtain ⟨c, hc⟩ := base.separation 2 phi (cons a.val (cons b.val Fin.elim0)) w
  have hc' : ∀ x, s x c ↔ s x w ∧ ((s x a.val ∧ ¬s x b.val) ∨ (s x b.val ∧ ¬s x a.val)) := by
    intro x
    have h := hc x
    simp only [phi, Eval, eval_disj] at h
    exact h
  refine ⟨⟨c, fun x hx => ((hc' x).mp hx).1⟩, fun x => ?_⟩
  exact (hc' x).trans ⟨fun h => h.2, fun h => ⟨h.elim
    (fun ha => a.property x ha.1) (fun hb => b.property x hb.1), h⟩⟩

noncomputable def internalMaskMul (base : BaseCollection s) {w : U}
    (a b : InternalMask s w) : InternalMask s w := Classical.choose (internal_mask_xor_exists base a b)

theorem internal_mask_mul_mem (base : BaseCollection s) {w : U} (a b : InternalMask s w) (x : U) :
    s x (internalMaskMul base a b).val ↔
      (s x a.val ∧ ¬s x b.val) ∨ (s x b.val ∧ ¬s x a.val) :=
  Classical.choose_spec (internal_mask_xor_exists base a b) x

theorem internal_mask_mul_comm (base : BaseCollection s) {w : U} (a b : InternalMask s w) :
    internalMaskMul base a b = internalMaskMul base b a := by
  apply internal_mask_ext base
  intro x
  rw [internal_mask_mul_mem base a b x, internal_mask_mul_mem base b a x]
  exact or_comm

theorem internal_mask_mul_self (base : BaseCollection s) {w : U} (a : InternalMask s w) :
    internalMaskMul base a a = internalMaskOne base w := by
  apply internal_mask_ext base
  intro x
  rw [internal_mask_mul_mem base a a x]
  simp [internal_mask_one_mem base w x]

noncomputable def internalMaskGroup (base : BaseCollection s) (w : U) :
    ExternalGroupData (InternalMask s w) where
  one := internalMaskOne base w
  mul := internalMaskMul base
  inv := id
  assoc := by
    intro a b c
    apply internal_mask_ext base
    intro x
    simp only [internal_mask_mul_mem]
    by_cases ha : s x a.val <;> by_cases hb : s x b.val <;> by_cases hc : s x c.val <;> simp [ha, hb, hc]
  one_mul := by
    intro a
    apply internal_mask_ext base
    intro x
    simp only [internal_mask_mul_mem, internal_mask_one_mem base w x, false_and, not_false_eq_true, and_true, false_or]
  mul_one := by
    intro a
    rw [internal_mask_mul_comm]
    apply internal_mask_ext base
    intro x
    simp only [internal_mask_mul_mem, internal_mask_one_mem base w x, false_and, not_false_eq_true, and_true, false_or]
  inv_mul := internal_mask_mul_self base
  mul_inv := internal_mask_mul_self base

noncomputable def internalMaskEnumeration (base : BaseCollection s) (w : U) (e : Nat → U)
    (n : Nat) : InternalMask s w := by
  classical
  exact if h : Subset s (e n) w then ⟨e n, h⟩ else internalMaskOne base w

theorem internal_mask_enumeration_onto (base : BaseCollection s) (w : U)
    (e : Nat → U) (he : ∀ x, ∃ n, e n = x) :
    ∀ a : InternalMask s w, ∃ n, internalMaskEnumeration base w e n = a := by
  intro a
  obtain ⟨n, hn⟩ := he a.val
  refine ⟨n, ?_⟩
  apply Subtype.ext
  have hsub : Subset s (e n) w := hn.symm ▸ a.property
  simp only [internalMaskEnumeration, dif_pos hsub]
  exact hn

/-- The finite stages are spans of finitely many entire internal masks.
    An individual mask may include nonstandardly many or infinitely many rows. -/
noncomputable def internalMaskExhaustion (base : BaseCollection s) (w : U)
    (e : Nat → U) (he : ∀ x, ∃ n, e n = x) : FiniteGroupExhaustion (internalMaskGroup base w) :=
  countableBooleanExhaustion (internalMaskGroup base w) (internal_mask_mul_comm base)
    (internal_mask_mul_self base) (internalMaskEnumeration base w e)
    (internal_mask_enumeration_onto base w e he)

#print axioms internalMaskExhaustion
end FullBridge
