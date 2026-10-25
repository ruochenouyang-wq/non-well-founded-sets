import InternalQuinePairs
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

noncomputable def standardOmegaValue (base : BaseCollection s) (z : U) : Nat → U
  | 0 => z
  | n+1 => Classical.choose (successor_exists base (standardOmegaValue base z n))

theorem standard_omega_values_mem (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (n : Nat) : s (standardOmegaValue base z n) w := by
  induction n with
  | zero => exact hw.2.1.1
  | succ n ih => exact hw.2.1.2 _ ih _ (Classical.choose_spec (successor_exists base _))

theorem standard_omega_values_injective (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) :
    ∀ n m, standardOmegaValue base z n = standardOmegaValue base z m → n = m := by
  intro n
  induction n with
  | zero =>
    intro m h
    cases m with
    | zero => rfl
    | succ m =>
      have hs := Classical.choose_spec (successor_exists base (standardOmegaValue base z m))
      have hm := (hs (standardOmegaValue base z m)).mpr (Or.inr rfl)
      change s (standardOmegaValue base z m) (standardOmegaValue base z (m+1)) at hm
      exact False.elim (hw.1 _ (h.symm ▸ hm))
  | succ n ih =>
    intro m h
    cases m with
    | zero =>
      have hs := Classical.choose_spec (successor_exists base (standardOmegaValue base z n))
      have hn := (hs (standardOmegaValue base z n)).mpr (Or.inr rfl)
      change s (standardOmegaValue base z n) (standardOmegaValue base z (n+1)) at hn
      exact False.elim (hw.1 _ (h ▸ hn))
    | succ m =>
      have hn : IsSuccessor s (standardOmegaValue base z n) (standardOmegaValue base z (n+1)) :=
        Classical.choose_spec (successor_exists base _)
      have hm : IsSuccessor s (standardOmegaValue base z m) (standardOmegaValue base z (m+1)) :=
        Classical.choose_spec (successor_exists base _)
      exact congrArg Nat.succ (ih m (internal_omega_successor_injective base hw
        (standard_omega_values_mem base hw n) hn (h.symm ▸ hm)))

/-- The internal family is indexed by all of the model's omega, which may
    contain nonstandard elements. The standard rows below need not cover it. -/
theorem bafa_omega_quine_pair_family (base : BaseCollection s) (hB : BAFACode s) :
    ∃ z w, ∃ P : InternalQuinePairs s w, OmegaCode s z w ∧
      ∃ row left right : Nat → U,
        (∀ n, s (row n) P.family ∧ IsPair s (row n) (left n) (right n) ∧
          SelfSingleton s (left n) ∧ SelfSingleton s (right n) ∧ left n ≠ right n) ∧
        (∀ n m, row n = row m → n = m) := by
  classical
  obtain ⟨z, w, hw⟩ := internal_omega_exists base
  obtain ⟨P⟩ := bafa_internal_quine_pairs base hB w
  let nu := standardOmegaValue base z
  have hn := standard_omega_values_mem base hw
  let left := fun n => Classical.choose (P.leftFunction.2 (nu n) (hn n))
  let right := fun n => Classical.choose (P.rightFunction.2 (nu n) (hn n))
  have hl := fun n => (Classical.choose_spec (P.leftFunction.2 (nu n) (hn n))).1
  have hr := fun n => (Classical.choose_spec (P.rightFunction.2 (nu n) (hn n))).1
  let row := fun n => Classical.choose (base.pairing (left n) (right n))
  have hp := fun n => Classical.choose_spec (base.pairing (left n) (right n))
  refine ⟨z, w, P, hw, row, left, right, ?_, ?_⟩
  · intro n
    exact ⟨(P.members _).mpr ⟨nu n, left n, right n, hn n, hl n, hr n, hp n⟩,
      hp n, P.leftQuine _ _ (hl n), P.rightQuine _ _ (hr n), internal_quine_pair_distinct P (hl n) (hr n)⟩
  · intro n m hnm
    have hx : s (left n) (row n) := (hp n (left n)).mpr (Or.inl rfl)
    have hy : s (left n) (row m) := by rw [← hnm]; exact hx
    have he := internal_quine_pair_rows_disjoint P (hl n) (hr n) (hl m) (hr m) (hp n) (hp m)
      hx hy
    exact standard_omega_values_injective base hw n m he

#print axioms bafa_omega_quine_pair_family
end FullBridge
