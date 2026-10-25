import StandardOmegaCut
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Retain the link to the actual source label functions. This extra
    information was existentially forgotten in the earlier API. -/
def OmegaSwapIndexed (base : BaseCollection s) {w : U} (z : U)
    (P : InternalQuinePairs s w) (S : PairSwapSequence s P.family) : Prop :=
  ∀ n, CodedRelation s P.leftCode (standardOmegaValue base z n) (S.action n).left ∧
    CodedRelation s P.rightCode (standardOmegaValue base z n) (S.action n).right

theorem indexed_pair_swap_at (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) {a x l r c : U}
    (P : InternalQuinePairs s a) (hl : CodedRelation s P.leftCode x l)
    (hr : CodedRelation s P.rightCode x r) (hp : IsPair s c l r) :
    ∃ A : PairSwapAt s P.family c, A.left = l ∧ A.right = r := by
  obtain ⟨j, hj, ho, hs, hlocal, hjl, hjr, hrows, hF, hother, _, hmove⟩ :=
    countable_bafa_internal_pair_swap base hB enum henum P hl hr
  exact ⟨⟨l, r, j, hp, internal_quine_pair_distinct P hl hr, hj, ho, hs, hlocal,
    hrows, hF, hjl, hjr, hother, hmove⟩, rfl, rfl⟩

theorem countable_bafa_omega_indexed_swaps (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) {z w : U} (hw : OmegaCode s z w) :
    ∃ P : InternalQuinePairs s w, ∃ S : PairSwapSequence s P.family,
      OmegaSwapIndexed base z P S ∧
      ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x) := by
  classical
  obtain ⟨P⟩ := bafa_internal_quine_pairs base hB w
  let nu := standardOmegaValue base z
  have hn := standard_omega_values_mem base hw
  let left := fun n => Classical.choose (P.leftFunction.2 (nu n) (hn n))
  let right := fun n => Classical.choose (P.rightFunction.2 (nu n) (hn n))
  have hl := fun n => (Classical.choose_spec (P.leftFunction.2 (nu n) (hn n))).1
  have hr := fun n => (Classical.choose_spec (P.rightFunction.2 (nu n) (hn n))).1
  let row := fun n => Classical.choose (base.pairing (left n) (right n))
  have hp := fun n => Classical.choose_spec (base.pairing (left n) (right n))
  have hrows : ∀ n, s (row n) P.family := fun n =>
    (P.members _).mpr ⟨nu n, left n, right n, hn n, hl n, hr n, hp n⟩
  have hi : ∀ n m, row n = row m → n = m := by
    intro n m hnm
    have hx := (hp n (left n)).mpr (Or.inl rfl)
    have hy : s (left n) (row m) := hnm ▸ hx
    exact standard_omega_values_injective base hw n m
      (internal_quine_pair_rows_disjoint P (hl n) (hr n) (hl m) (hr m) (hp n) (hp m) hx hy)
  have hex := fun n => indexed_pair_swap_at base hB enum henum P (hl n) (hr n) (hp n)
  let action := fun n => Classical.choose (hex n)
  have ha := fun n => Classical.choose_spec (hex n)
  let S : PairSwapSequence s P.family := {
    row := row
    row_mem := hrows
    row_injective := hi
    quines := by
      intro b y hb hy
      obtain ⟨x, l, r, _, hxl, hxr, hpair⟩ := (P.members b).mp hb
      rcases (hpair y).mp hy with rfl | rfl
      · exact P.leftQuine x _ hxl
      · exact P.rightQuine x _ hxr
    disjoint_rows := fun b c y hb hc hyb hyc => internal_pair_family_disjoint P base hb hc hyb hyc
    nonempty_rows := by
      intro b hb
      obtain ⟨_, l, _, _, _, _, hpair⟩ := (P.members b).mp hb
      exact ⟨l, (hpair l).mpr (Or.inl rfl)⟩
    action := action }
  have hidx : OmegaSwapIndexed base z P S := by
    intro n
    exact ⟨(ha n).1.symm ▸ hl n, (ha n).2.symm ▸ hr n⟩
  obtain ⟨T, _, hlabels, hc⟩ := pair_sequence_commuting_extension base hB enum henum S
  refine ⟨P, T, ?_, hc⟩
  intro n
  exact ⟨(hlabels n).1.symm ▸ (hidx n).1, (hlabels n).2.symm ▸ (hidx n).2⟩

#print axioms countable_bafa_omega_indexed_swaps
end FullBridge
