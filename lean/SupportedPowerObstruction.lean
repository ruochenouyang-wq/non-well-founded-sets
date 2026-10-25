import SupportedSeparation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The actual internally coded selector range is moved by every selected
    swap, since the rows are disjoint and the selected element is unique. -/
theorem pair_sequence_moves_choice_range {F f L : U} (S : PairSwapSequence s F)
    (hf : ChoiceFunctionCode s F f) (hL : CodedImageSet s f F L) (n : Nat) : S.map n L ≠ L := by
  intro hfix
  obtain ⟨y, hy, huniq⟩ := hf.1.2 (S.row n) (S.row_mem n)
  have hym := hf.2 (S.row n) (S.row_mem n) y hy
  have hyL := (hL y).mpr ⟨S.row n, S.row_mem n, hy⟩
  have hm : ∀ x z, s x z ↔ s (S.map n x) (S.map n z) := fun x z => by
    exact (S.action n).elementary (Formula.member (n := 2) 0 1) (cons x (cons z Fin.elim0))
  have hjyL : s (S.map n y) L := hfix ▸ (hm y L).mp hyL
  obtain ⟨c, hc, hcyj⟩ := (hL _).mp hjyL
  have hjym : s (S.map n y) (S.row n) := (S.action n).fix_rows _ (S.row_mem n) ▸ (hm y (S.row n)).mp hym
  have hcEq := S.disjoint_rows c (S.row n) (S.map n y) hc (S.row_mem n) (hf.2 c hc _ hcyj) hjym
  subst c
  have he := huniq (S.map n y) hcyj
  rcases ((S.action n).pair y).mp hym with h | h
  · change (S.action n).map y = y at he
    rw [h, (S.action n).swap_left] at he
    exact (S.action n).distinct he.symm
  · change (S.action n).map y = y at he
    rw [h, (S.action n).swap_right] at he
    exact (S.action n).distinct he

theorem pair_sequence_choice_range_excluded (base : BaseCollection s) {F f : U}
    (S : PairSwapSequence s F) (hf : ChoiceFunctionCode s F f) :
    ∃ d L, HereditarilyEventuallyFixed s S.map d ∧
      (∀ y, s y d ↔ ∃ c, s c F ∧ s y c) ∧ CodedImageSet s f F L ∧ Subset s L d ∧
      ¬ HereditarilyEventuallyFixed s S.map L := by
  obtain ⟨d, hd⟩ := base.union F
  obtain ⟨L, hL⟩ := coded_image_set_exists base f F
  refine ⟨d, L, hereditary_support_union base (fun n => (S.action n).elementary)
    (fun n => (S.action n).onto) (pair_sequence_family_hereditarily_supported S) hd, hd, hL, ?_, ?_⟩
  · intro y hy
    obtain ⟨c, hc, hcy⟩ := (hL y).mp hy
    exact (hd y).mpr ⟨c, hc, hf.2 c hc y hcy⟩
  · intro h
    obtain ⟨N, hN⟩ := hereditary_support_root h
    exact pair_sequence_moves_choice_range S hf hL N (hN N (Nat.le_refl N))

/-- This rules out inheriting the ambient powerset literally; it does not
    rule out a different source set containing precisely supported subsets. -/
theorem pair_sequence_ambient_powerset_excluded (base : BaseCollection s) {F f : U}
    (S : PairSwapSequence s F) (hf : ChoiceFunctionCode s F f) :
    ∃ d p, HereditarilyEventuallyFixed s S.map d ∧
      (∀ x, s x p ↔ Subset s x d) ∧ ¬ HereditarilyEventuallyFixed s S.map p := by
  obtain ⟨d, L, hdH, _, _, hLd, hLH⟩ := pair_sequence_choice_range_excluded base S hf
  obtain ⟨p, hp⟩ := base.powerset d
  exact ⟨d, p, hdH, hp, fun h => hLH (hereditary_support_member h ((hp L).mpr hLd))⟩

/-- Keep the ambient selector as evidence while constructing the sequence.
    Its existence comes from the label maps, not from object Choice. -/
theorem bafa_pair_sequence_with_ambient_choice (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ F, ∃ _S : PairSwapSequence s F, ∃ f, ChoiceFunctionCode s F f := by
  obtain ⟨_, _, P, _, row, _, _, hrows, hi⟩ := bafa_omega_quine_pair_family base hB
  have hs : Nonempty (PairSwapSequence s P.family) := by
    refine ⟨⟨row, fun n => (hrows n).1, hi, ?_, ?_, ?_, ?_⟩⟩
    · intro b y hb hy
      obtain ⟨x, l, r, _, hl, hr, hp⟩ := (P.members b).mp hb
      rcases (hp y).mp hy with rfl | rfl
      · exact P.leftQuine x _ hl
      · exact P.rightQuine x _ hr
    · intro b c y hb hc hyb hyc
      exact internal_pair_family_disjoint P base hb hc hyb hyc
    · intro b hb
      obtain ⟨_, l, _, _, _, _, hp⟩ := (P.members b).mp hb
      exact ⟨l, (hp l).mpr (Or.inl rfl)⟩
    · intro n
      exact Classical.choice (internal_pair_swap_at base hB enum henum P ((hrows n).1))
  obtain ⟨S⟩ := hs
  exact ⟨P.family, S, internal_quine_pairs_have_choice base P⟩

/-- The very same actual no-choice candidate has an inherited-powerset
    obstruction. This is not a proof that its own PowerSet axiom fails. -/
theorem countable_bafa_supported_candidate_power_obstruction (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ F, ∃ S : PairSwapSequence s F,
      HereditarilyEventuallyFixed s S.map F ∧
      Extensional (supportedMember (s := s) S.map) ∧ Empty (supportedMember (s := s) S.map) ∧
      Pairing (supportedMember (s := s) S.map) ∧ Union (supportedMember (s := s) S.map) ∧
      Infinity (supportedMember (s := s) S.map) ∧ BoundedSeparation (supportedMember (s := s) S.map) ∧
      ¬ ChoiceCode (supportedMember (s := s) S.map) ∧
      ∃ d p, HereditarilyEventuallyFixed s S.map d ∧
        (∀ x, s x p ↔ Subset s x d) ∧ ¬ HereditarilyEventuallyFixed s S.map p := by
  obtain ⟨F, S, f, hf⟩ := bafa_pair_sequence_with_ambient_choice base hB enum henum
  exact ⟨F, S, pair_sequence_family_hereditarily_supported S,
    supported_carrier_extensional base.extensional S.map,
    supported_carrier_empty base S.map (fun n => (S.action n).elementary) (fun n => (S.action n).onto),
    supported_carrier_pairing base S.map (fun n => (S.action n).elementary),
    supported_carrier_union base S.map (fun n => (S.action n).elementary) (fun n => (S.action n).onto),
    supported_carrier_infinity base S.map (fun n => (S.action n).locally_internal),
    supported_carrier_bounded_separation base S.map (fun n => (S.action n).elementary) (fun n => (S.action n).onto),
    pair_sequence_supported_carrier_not_choice S, pair_sequence_ambient_powerset_excluded base S hf⟩

#print axioms countable_bafa_supported_candidate_power_obstruction
end FullBridge
