import IndexedSelectorPrefixes
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- An exact relative powerset of the label union would make the external
    standard cut a source set, via a genuine first-order separation. -/
theorem indexed_power_trace_defines_standard_cut (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (S : PairSwapSequence s P.family)
    (hidx : OmegaSwapIndexed base z P S) {d p : U}
    (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c)
    (hp : ∀ L, s L p ↔ HereditarilyEventuallyFixed s S.map L ∧ Subset s L d) :
    ∃ c, ∀ x, s x c ↔ ∃ n, x = standardOmegaValue base z n := by
  let phi : Formula 3 := .ex (.conj (codedImageSetFormula 2 1 0) (.member 0 3))
  have hev : ∀ x, Eval s phi (cons x (cons P.leftCode (cons p Fin.elim0))) ↔
      ∃ L, CodedImageSet s P.leftCode x L ∧ s L p := by
    intro x
    simp only [phi, Eval, eval_codedImageSetFormula]
    rfl
  obtain ⟨c, hc⟩ := base.separation 2 phi (cons P.leftCode (cons p Fin.elim0)) w
  refine ⟨c, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨hxw, hxphi⟩ := (hc x).mp hx
    obtain ⟨L, hL, hLp⟩ := (hev x).mp hxphi
    exact (indexed_prefix_supported_iff_standard base hw P S hidx hxw hL).mp ((hp L).mp hLp).1
  · rintro ⟨n, rfl⟩
    obtain ⟨L, hL⟩ := coded_image_set_exists base P.leftCode (standardOmegaValue base z n)
    apply (hc _).mpr
    refine ⟨standard_omega_values_mem base hw n, (hev _).mpr ⟨L, hL, ?_⟩⟩
    exact (hp L).mpr ⟨indexed_standard_prefix_supported base hw P S hidx n hL,
      left_prefix_subset_union base P hL hd⟩

theorem indexed_nonstandard_no_relative_power_trace (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (S : PairSwapSequence s P.family)
    (hidx : OmegaSwapIndexed base z P S)
    (hns : ∃ a, s a w ∧ ∀ n, a ≠ standardOmegaValue base z n) {d : U}
    (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c) :
    ¬ ∃ p, ∀ L, s L p ↔ HereditarilyEventuallyFixed s S.map L ∧ Subset s L d := by
  rintro ⟨p, hp⟩
  exact standard_omega_cut_not_internal base hw hns
    (indexed_power_trace_defines_standard_cut base hw P S hidx hd hp)

/-- This refutes the subtype's own PowerSet axiom, not only inheritance
    of the ambient powerset. No source Choice is used. -/
theorem indexed_nonstandard_supported_not_powerset (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (S : PairSwapSequence s P.family)
    (hidx : OmegaSwapIndexed base z P S)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x))
    (hns : ∃ a, s a w ∧ ∀ n, a ≠ standardOmegaValue base z n) :
    ¬ PowerSet (supportedMember (s := s) S.map) := by
  intro hpower
  obtain ⟨d, hd⟩ := base.union P.family
  have hD := hereditary_support_union base (fun n => (S.action n).elementary)
    (fun n => (S.action n).onto) (pair_sequence_family_hereditarily_supported S) hd
  obtain ⟨p, hp⟩ := (supported_power_iff_traces base S hc).mp hpower ⟨d, hD⟩
  exact indexed_nonstandard_no_relative_power_trace base hw P S hidx hns hd ⟨p, hp⟩

theorem indexed_supported_powerset_requires_standard_omega (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (S : PairSwapSequence s P.family)
    (hidx : OmegaSwapIndexed base z P S)
    (hc : ∀ n m x, S.map n (S.map m x) = S.map m (S.map n x))
    (hpower : PowerSet (supportedMember (s := s) S.map)) :
    ∀ a, s a w → ∃ n, a = standardOmegaValue base z n := by
  classical
  intro a ha
  apply Classical.byContradiction
  intro hns
  exact indexed_nonstandard_supported_not_powerset base hw P S hidx hc
    ⟨a, ha, fun n he => hns ⟨n, he⟩⟩ hpower

/-- For every countable BAFA source with a nonstandard internal natural,
    the actual standard-indexed commuting construction supplies a
    candidate satisfying the earlier basic axioms but failing PowerSet. -/
theorem countable_bafa_nonstandard_supported_power_failure
    (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) {z w : U}
    (hw : OmegaCode s z w)
    (hns : ∃ a, s a w ∧ ∀ n, a ≠ standardOmegaValue base z n) :
    ∃ P : InternalQuinePairs s w, ∃ S : PairSwapSequence s P.family,
      OmegaSwapIndexed base z P S ∧
      (∀ n m x, S.map n (S.map m x) = S.map m (S.map n x)) ∧
      HereditarilyEventuallyFixed s S.map P.family ∧
      Extensional (supportedMember (s := s) S.map) ∧ Empty (supportedMember (s := s) S.map) ∧
      Pairing (supportedMember (s := s) S.map) ∧ Union (supportedMember (s := s) S.map) ∧
      Infinity (supportedMember (s := s) S.map) ∧ BoundedSeparation (supportedMember (s := s) S.map) ∧
      ¬ ChoiceCode (supportedMember (s := s) S.map) ∧ ¬ PowerSet (supportedMember (s := s) S.map) := by
  obtain ⟨P, S, hidx, hc⟩ := countable_bafa_omega_indexed_swaps base hB enum henum hw
  exact ⟨P, S, hidx, hc, pair_sequence_family_hereditarily_supported S,
    supported_carrier_extensional base.extensional S.map,
    supported_carrier_empty base S.map (fun n => (S.action n).elementary) (fun n => (S.action n).onto),
    supported_carrier_pairing base S.map (fun n => (S.action n).elementary),
    supported_carrier_union base S.map (fun n => (S.action n).elementary) (fun n => (S.action n).onto),
    supported_carrier_infinity base S.map (fun n => (S.action n).locally_internal),
    supported_carrier_bounded_separation base S.map (fun n => (S.action n).elementary) (fun n => (S.action n).onto),
    pair_sequence_supported_carrier_not_choice S,
    indexed_nonstandard_supported_not_powerset base hw P S hidx hc hns⟩

#print axioms indexed_nonstandard_supported_not_powerset
#print axioms countable_bafa_nonstandard_supported_power_failure
end FullBridge
