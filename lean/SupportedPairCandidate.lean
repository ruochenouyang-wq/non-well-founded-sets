import SupportedCoding
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

structure PairSwapAt (s : U → U → Prop) (F c : U) where
  left : U
  right : U
  map : U → U
  pair : IsPair s c left right
  distinct : left ≠ right
  elementary : ElementaryMap s s map
  onto : ∀ y, ∃ x, map x = y
  involutive : ∀ x, map (map x) = x
  locally_internal : LocallyInternalTransitiveMap s map
  fix_rows : ∀ b, s b F → map b = b
  fix_family : map F = F
  swap_left : map left = right
  swap_right : map right = left
  fix_other : ∀ b y, s b F → s y b → y ≠ left → y ≠ right → map y = y
  moves_choice : ∀ f, ChoiceFunctionCode s F f → map f ≠ f

structure PairSwapSequence (s : U → U → Prop) (F : U) where
  row : Nat → U
  row_mem : ∀ n, s (row n) F
  row_injective : ∀ n m, row n = row m → n = m
  quines : ∀ b y, s b F → s y b → SelfSingleton s y
  disjoint_rows : ∀ b c y, s b F → s c F → s y b → s y c → b = c
  nonempty_rows : ∀ b, s b F → ∃ y, s y b
  action : ∀ n, PairSwapAt s F (row n)

def PairSwapSequence.map {F : U} (S : PairSwapSequence s F) : Nat → U → U := fun n => (S.action n).map

theorem internal_pair_family_disjoint {a : U} (P : InternalQuinePairs s a)
    (base : BaseCollection s) {b c y : U} (hb : s b P.family) (hc : s c P.family)
    (hyb : s y b) (hyc : s y c) : b = c := by
  obtain ⟨i, l, r, _, hl, hr, hp⟩ := (P.members b).mp hb
  obtain ⟨k, L, R, _, hL, hR, hP⟩ := (P.members c).mp hc
  have he := internal_quine_pair_rows_disjoint P hl hr hL hR hp hP hyb hyc
  subst k
  have hLl := coded_function_value_unique P.leftFunction hL hl
  have hRr := coded_function_value_unique P.rightFunction hR hr
  subst L; subst R
  exact pair_unique base.extensional hp hP

theorem internal_pair_swap_at (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) {a c : U}
    (P : InternalQuinePairs s a) (hc : s c P.family) : Nonempty (PairSwapAt s P.family c) := by
  obtain ⟨x, l, r, _, hl, hr, hp⟩ := (P.members c).mp hc
  obtain ⟨j, hj, ho, hs, hlocal, hjl, hjr, hrows, hF, hother, _, hmove⟩ :=
    countable_bafa_internal_pair_swap base hB enum henum P hl hr
  exact ⟨⟨l, r, j, hp, internal_quine_pair_distinct P hl hr, hj, ho, hs, hlocal, hrows, hF, hjl, hjr, hother, hmove⟩⟩

/-- The sequence is constructed, not supplied as an extra model hypothesis.
    Its selected rows are distinct, but need not exhaust the internal family. -/
theorem bafa_internal_pair_swap_sequence (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ F, Nonempty (PairSwapSequence s F) := by
  obtain ⟨_, _, P, _, row, _, _, hrows, hi⟩ := bafa_omega_quine_pair_family base hB
  refine ⟨P.family, ⟨⟨row, fun n => (hrows n).1, hi, ?_, ?_, ?_, ?_⟩⟩⟩
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

theorem pair_sequence_labels_eventually_fixed {F : U} (S : PairSwapSequence s F)
    {b y : U} (hb : s b F) (hy : s y b) : EventuallyFixedBy S.map y := by
  classical
  by_cases hex : ∃ m, s y (S.row m)
  · obtain ⟨m, hm⟩ := hex
    refine ⟨m+1, fun n hn => ?_⟩
    have hrows : S.row n ≠ S.row m := by
      intro h
      have hnm := S.row_injective n m h
      subst n
      exact Nat.not_succ_le_self m hn
    have hl : y ≠ (S.action n).left := by
      intro he
      have hyn := ((S.action n).pair y).mpr (Or.inl he)
      exact hrows (S.disjoint_rows _ _ y (S.row_mem n) (S.row_mem m) hyn hm)
    have hr : y ≠ (S.action n).right := by
      intro he
      have hyn := ((S.action n).pair y).mpr (Or.inr he)
      exact hrows (S.disjoint_rows _ _ y (S.row_mem n) (S.row_mem m) hyn hm)
    exact (S.action n).fix_other b y hb hy hl hr
  · refine ⟨0, fun n _ => ?_⟩
    exact (S.action n).fix_other b y hb hy
      (fun he => hex ⟨n, ((S.action n).pair y).mpr (Or.inl he)⟩)
      (fun he => hex ⟨n, ((S.action n).pair y).mpr (Or.inr he)⟩)

theorem pair_sequence_family_hereditarily_supported {F : U} (S : PairSwapSequence s F) :
    HereditarilyEventuallyFixed s S.map F := by
  apply hereditary_support_intro ⟨0, fun n _ => (S.action n).fix_family⟩
  intro b hb
  apply hereditary_support_intro ⟨0, fun n _ => (S.action n).fix_rows b hb⟩
  intro y hy
  exact hereditary_support_quine (S.quines b y hb hy) (pair_sequence_labels_eventually_fixed S hb hy)

theorem pair_sequence_supported_carrier_not_choice {F : U} (S : PairSwapSequence s F) :
    ¬ ChoiceCode (supportedMember (s := s) S.map) :=
  supported_carrier_choice_obstruction (pair_sequence_family_hereditarily_supported S)
    S.nonempty_rows (fun n => (S.action n).moves_choice)

/-- An actual hereditary substructure with failed Choice and verified basic
    closure. PowerSet, Infinity, Separation, Collection and BAFA are not claimed
    for it here. It is not yet a full set-theoretic symmetric model. -/
theorem countable_bafa_supported_pair_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ F, ∃ S : PairSwapSequence s F,
      HereditarilyEventuallyFixed s S.map F ∧
      Extensional (supportedMember (s := s) S.map) ∧ Empty (supportedMember (s := s) S.map) ∧
      Pairing (supportedMember (s := s) S.map) ∧ Union (supportedMember (s := s) S.map) ∧
      ¬ ChoiceCode (supportedMember (s := s) S.map) := by
  obtain ⟨F, ⟨S⟩⟩ := bafa_internal_pair_swap_sequence base hB enum henum
  exact ⟨F, S, pair_sequence_family_hereditarily_supported S,
    supported_carrier_extensional base.extensional S.map,
    supported_carrier_empty base S.map (fun n => (S.action n).elementary) (fun n => (S.action n).onto),
    supported_carrier_pairing base S.map (fun n => (S.action n).elementary),
    supported_carrier_union base S.map (fun n => (S.action n).elementary) (fun n => (S.action n).onto),
    pair_sequence_supported_carrier_not_choice S⟩

#print axioms countable_bafa_supported_pair_candidate
end FullBridge
