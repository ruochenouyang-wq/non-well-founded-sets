import IndexedOmegaSwaps
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem internal_left_label_row (base : BaseCollection s) {w : U}
    (P : InternalQuinePairs s w) {i y : U} (hy : CodedRelation s P.leftCode i y) :
    ∃ c, s c P.family ∧ s y c := by
  have hi := coded_function_domain P.leftFunction hy
  obtain ⟨r, hr, _⟩ := P.rightFunction.2 i hi
  obtain ⟨c, hc⟩ := base.pairing y r
  exact ⟨c, (P.members c).mpr ⟨i, y, r, hi, hy, hr, hc⟩, (hc y).mpr (Or.inl rfl)⟩

theorem indexed_left_label_fixed (base : BaseCollection s) {z w : U}
    (P : InternalQuinePairs s w) (S : PairSwapSequence s P.family)
    (hidx : OmegaSwapIndexed base z P S) {i y : U}
    (hy : CodedRelation s P.leftCode i y) (n : Nat)
    (hne : i ≠ standardOmegaValue base z n) : S.map n y = y := by
  obtain ⟨c, hc, hyc⟩ := internal_left_label_row base P hy
  apply (S.action n).fix_other c y hc hyc
  · intro he
    exact hne (P.leftInjective i _ y hy (he.symm ▸ (hidx n).1))
  · intro he
    exact P.disjoint i _ y hy (he.symm ▸ (hidx n).2)

theorem indexed_standard_prefix_supported (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (S : PairSwapSequence s P.family)
    (hidx : OmegaSwapIndexed base z P S) (k : Nat) {L : U}
    (hL : CodedImageSet s P.leftCode (standardOmegaValue base z k) L) :
    HereditarilyEventuallyFixed s S.map L := by
  have hfixed : ∀ y, s y L → ∀ n, k ≤ n → S.map n y = y := by
    intro y hy n hn
    obtain ⟨i, hi, hiy⟩ := (hL y).mp hy
    obtain ⟨j, hj, rfl⟩ := (standard_omega_members base hw k i).mp hi
    apply indexed_left_label_fixed base P S hidx hiy n
    intro he
    have hjn := standard_omega_values_injective base hw j n he
    subst j
    exact Nat.not_lt_of_ge hn hj
  apply hereditary_support_intro
  · refine ⟨k, fun n hn => ?_⟩
    exact elementary_map_fixed_members_set base (S.action n).elementary (S.action n).onto
      (fun y hy => hfixed y hy n hn)
  · intro y hy
    obtain ⟨i, _, hiy⟩ := (hL y).mp hy
    exact hereditary_support_quine (P.leftQuine i y hiy) ⟨k, hfixed y hy⟩

theorem indexed_prefix_moved (base : BaseCollection s) {z w : U}
    (P : InternalQuinePairs s w) (S : PairSwapSequence s P.family)
    (hidx : OmegaSwapIndexed base z P S) {a L : U}
    (hL : CodedImageSet s P.leftCode a L) (n : Nat)
    (hn : s (standardOmegaValue base z n) a) : S.map n L ≠ L := by
  intro hfix
  have hl := (hL _).mpr ⟨standardOmegaValue base z n, hn, (hidx n).1⟩
  have hm : s (S.action n).left L ↔ s (S.map n (S.action n).left) (S.map n L) :=
    (S.action n).elementary (Formula.member (n := 2) 0 1)
      (cons (S.action n).left (cons L Fin.elim0))
  have hr := hm.mp hl
  change s ((S.action n).map (S.action n).left) (S.map n L) at hr
  rw [(S.action n).swap_left, hfix] at hr
  obtain ⟨i, _, hi⟩ := (hL _).mp hr
  exact P.disjoint i _ _ hi (hidx n).2

/-- Prefix selectors detect exactly the external standard cut of omega. -/
theorem indexed_prefix_supported_iff_standard (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (S : PairSwapSequence s P.family)
    (hidx : OmegaSwapIndexed base z P S) {a L : U} (ha : s a w)
    (hL : CodedImageSet s P.leftCode a L) :
    HereditarilyEventuallyFixed s S.map L ↔ ∃ n, a = standardOmegaValue base z n := by
  classical
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hns
    have haAll := nonstandard_omega_contains_all_standard base hw ha
      (fun n he => hns ⟨n, he⟩)
    obtain ⟨N, hN⟩ := hereditary_support_root hH
    exact indexed_prefix_moved base P S hidx hL N (haAll N) (hN N (Nat.le_refl N))
  · rintro ⟨n, rfl⟩
    exact indexed_standard_prefix_supported base hw P S hidx n hL

theorem left_prefix_subset_union (base : BaseCollection s) {w : U}
    (P : InternalQuinePairs s w) {a L d : U}
    (hL : CodedImageSet s P.leftCode a L)
    (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c) : Subset s L d := by
  intro y hy
  obtain ⟨i, _, hiy⟩ := (hL y).mp hy
  exact (hd y).mpr (internal_left_label_row base P hiy)

#print axioms indexed_prefix_supported_iff_standard
end FullBridge
