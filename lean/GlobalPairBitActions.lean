import PairBitCore
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem pair_family_global_bit_action (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) {F : U} (S : PairSwapSequence s F) :
    ∃ J : FiniteBitMask → U → U,
      (∀ g, ElementaryMap s s (J g) ∧ (∀ y, ∃ x, J g x = y) ∧ LocallyInternalTransitiveMap s (J g)) ∧
      (∀ x, J bitMaskOne x = x) ∧ (∀ g h x, J (bitMaskMul g h) x = J g (J h x)) ∧
      (∀ g h, (∀ x, J g x = J h x) → g = h) ∧
      (∀ g x, internalCode base (J g x) = internalCode base x) ∧
      (∀ n c y, s c F → s y c → J (singleBitMask n) y = pairLocalFlip S n y) := by
  obtain ⟨d, A, hd, _, hCodes⟩ := pair_family_bit_core base S
  have hAA : GroupActionExtends (A.stage 0) (A.stage 0) := ⟨fun _ hx => hx, fun _ _ _ h => h⟩
  obtain ⟨J, hJ, hOne, hMul, _, hCore, hFaith, hQ, _⟩ :=
    countable_bafa_controlled_group_extension base hB A (A.stage 0) hAA enum henum
  refine ⟨J, hJ, hOne, hMul, hFaith, hQ, ?_⟩
  intro n c y hc hy
  let v : Fin (n+1) → Bool := fun i => if i.val = n then true else false
  have hR := (hCodes (n+1) v y (pairLocalFlip S n y)).mpr
    ⟨(hd y).mpr ⟨c, hc, hy⟩, (finite_involution_action_last_bit (pairLocalFlip S) n y).symm⟩
  have h := hCore (n+1) v y _ hR
  change J (prefixBitMask (n+1) v) y = _ at h
  simpa only [v, prefix_last_bit_mask] using h

theorem bit_action_generator_involutive (J : FiniteBitMask → U → U)
    (hOne : ∀ x, J bitMaskOne x = x) (hMul : ∀ g h x, J (bitMaskMul g h) x = J g (J h x)) (n : Nat) (x : U) :
    J (singleBitMask n) (J (singleBitMask n) x) = x := by
  have he : bitMaskMul (singleBitMask n) (singleBitMask n) = bitMaskOne := finiteBitMaskGroup.inv_mul _
  rw [← hMul, he, hOne]

theorem controlled_pair_swap_at (base : BaseCollection s) {F : U} (S : PairSwapSequence s F)
    (J : FiniteBitMask → U → U)
    (hJ : ∀ g, ElementaryMap s s (J g) ∧ (∀ y, ∃ x, J g x = y) ∧ LocallyInternalTransitiveMap s (J g))
    (hOne : ∀ x, J bitMaskOne x = x) (hMul : ∀ g h x, J (bitMaskMul g h) x = J g (J h x))
    (hLocal : ∀ n c y, s c F → s y c → J (singleBitMask n) y = pairLocalFlip S n y) (n : Nat) :
    ∃ A : PairSwapAt s F (S.row n), A.map = J (singleBitMask n) ∧
      A.left = (S.action n).left ∧ A.right = (S.action n).right := by
  classical
  let j := J (singleBitMask n)
  have hj : ElementaryMap s s j := (hJ (singleBitMask n)).1
  have ho := (hJ (singleBitMask n)).2.1
  have hleft : j (S.action n).left = (S.action n).right := by
    simpa [pairLocalFlip, quineSwap] using
      hLocal n (S.row n) (S.action n).left (S.row_mem n) (((S.action n).pair _).mpr (Or.inl rfl))
  have hright : j (S.action n).right = (S.action n).left := by
    simpa [pairLocalFlip, quineSwap, Ne.symm (S.action n).distinct] using
      hLocal n (S.row n) (S.action n).right (S.row_mem n) (((S.action n).pair _).mpr (Or.inr rfl))
  have hother : ∀ c y, s c F → s y c → y ≠ (S.action n).left → y ≠ (S.action n).right → j y = y := by
    intro c y hc hy hyl hyr
    simpa [pairLocalFlip, quineSwap, hyl, hyr] using hLocal n c y hc hy
  have hrows : ∀ c, s c F → j c = c := by
    intro c hc
    by_cases he : c = S.row n
    · subst c
      have hpair := elementary_map_pair hj (S.action n).pair
      rw [hleft, hright] at hpair
      exact pair_unique base.extensional hpair (fun y => ((S.action n).pair y).trans or_comm)
    · apply elementary_map_fixed_members_set base hj ho
      intro y hy
      apply hother c y hc hy
      · intro heq
        exact he (S.disjoint_rows c (S.row n) y hc (S.row_mem n) hy
          (((S.action n).pair y).mpr (Or.inl heq)))
      · intro heq
        exact he (S.disjoint_rows c (S.row n) y hc (S.row_mem n) hy
          (((S.action n).pair y).mpr (Or.inr heq)))
  refine ⟨⟨(S.action n).left, (S.action n).right, j, (S.action n).pair, (S.action n).distinct,
    hj, ho, bit_action_generator_involutive J hOne hMul n, (hJ (singleBitMask n)).2.2,
    hrows, elementary_map_fixed_members_set base hj ho hrows, hleft, hright, hother, ?_⟩, rfl, rfl, rfl⟩
  intro f hf
  exact pair_swap_moves_internal_choice hj (S.row_mem n) (S.action n).pair (S.action n).distinct
    (hrows _ (S.row_mem n)) hleft hright hf

/-- Replace independently extended swaps by commuting full-model swaps,
    preserving exactly the selected rows and their left/right labels. -/
theorem pair_sequence_commuting_extension (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) {F : U} (S : PairSwapSequence s F) :
    ∃ T : PairSwapSequence s F, T.row = S.row ∧
      (∀ n, (T.action n).left = (S.action n).left ∧ (T.action n).right = (S.action n).right) ∧
      (∀ n m x, T.map n (T.map m x) = T.map m (T.map n x)) := by
  classical
  obtain ⟨J, hJ, hOne, hMul, _, _, hLocal⟩ := pair_family_global_bit_action base hB enum henum S
  have hex := fun n => controlled_pair_swap_at base S J hJ hOne hMul hLocal n
  let action := fun n => Classical.choose (hex n)
  have ha := fun n => Classical.choose_spec (hex n)
  let T : PairSwapSequence s F := ⟨S.row, S.row_mem, S.row_injective, S.quines, S.disjoint_rows, S.nonempty_rows, action⟩
  refine ⟨T, rfl, fun n => (ha n).2, ?_⟩
  intro n m x
  change (action n).map ((action m).map x) = (action m).map ((action n).map x)
  rw [(ha n).1, (ha m).1]
  exact group_action_preserves_commutation finiteBitMaskGroup J hMul (finite_bit_mask_commutative _ _) x

theorem countable_bafa_commuting_pair_sequence (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ F, ∃ S : PairSwapSequence s F, ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x) := by
  obtain ⟨F, ⟨S⟩⟩ := bafa_internal_pair_swap_sequence base hB enum henum
  obtain ⟨T, _, _, hc⟩ := pair_sequence_commuting_extension base hB enum henum S
  exact ⟨F, T, hc⟩

#print axioms countable_bafa_commuting_pair_sequence
end FullBridge
