import OmegaQuinePairs
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def pairLeftSelectionFormula {n} (l r c y : Fin n) : Formula n :=
  .ex (.conj (pairImagesFormula l.succ r.succ 0 c.succ) (relatedFormula l.succ 0 y.succ))

theorem eval_pairLeftSelectionFormula {n} (l r c y : Fin n) (v : Fin n → U) :
    Eval s (pairLeftSelectionFormula l r c y) v ↔
      ∃ x L R, CodedRelation s (v l) x L ∧ CodedRelation s (v r) x R ∧
        IsPair s (v c) L R ∧ CodedRelation s (v l) x (v y) := by
  simp only [pairLeftSelectionFormula, Eval, eval_pairImagesFormula, eval_relatedFormula, cons_succ, cons_zero]
  constructor
  · rintro ⟨x, ⟨L, R, hL, hR, hc⟩, hy⟩; exact ⟨x, L, R, hL, hR, hc, hy⟩
  · rintro ⟨x, L, R, hL, hR, hc, hy⟩; exact ⟨x, ⟨L, R, hL, hR, hc⟩, hy⟩

/-- The retained left-label code gives an actual choice function in the ambient
    model, without any assumption of object AC. A symmetric submodel must not
    retain this selector if this family is to witness failure of choice. -/
theorem internal_quine_pairs_have_choice (base : BaseCollection s) {a : U}
    (P : InternalQuinePairs s a) : ∃ f, ChoiceFunctionCode s P.family f := by
  obtain ⟨b, hb⟩ := codedRelation_component_bound base.union P.leftCode
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union P.family b
  obtain ⟨f, hf⟩ := relation_comprehension_members base (pairLeftSelectionFormula (n := 4) 2 3 1 0)
    (cons P.leftCode (cons P.rightCode Fin.elim0)) d
  have hev := fun c y => eval_pairLeftSelectionFormula (s := s) (n := 4) 2 3 1 0
    (cons y (cons c (cons P.leftCode (cons P.rightCode Fin.elim0))))
  have hFam : ∀ c y, (∃ x L R, CodedRelation s P.leftCode x L ∧ CodedRelation s P.rightCode x R ∧
      IsPair s c L R ∧ CodedRelation s P.leftCode x y) → s c P.family ∧ s y b := by
    rintro c y ⟨x, L, R, hL, hR, hc, hy⟩
    exact ⟨(P.members c).mpr ⟨x, L, R, coded_function_domain P.leftFunction hL, hL, hR, hc⟩,
      (hb x y hy).2⟩
  have hRel : ∀ c y, CodedRelation s f c y ↔
      ∃ x L R, CodedRelation s P.leftCode x L ∧ CodedRelation s P.rightCode x R ∧
        IsPair s c L R ∧ CodedRelation s P.leftCode x y := by
    intro c y
    constructor
    · rintro ⟨p, hp, hpc⟩
      obtain ⟨c', y', _, _, hp', hev'⟩ := (hf p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpc hp'
      exact (hev c y).mp hev'
    · intro h
      obtain ⟨hc, hy⟩ := hFam c y h
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing c y
      exact ⟨p, (hf p).mpr ⟨c, y, (hd c).mpr (Or.inl hc), (hd y).mpr (Or.inr hy), hp,
        (hev c y).mpr h⟩, hp⟩
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨c, y, _, _, hpc, he⟩ := (hf p).mp hp
    exact ⟨c, y, (hFam c y ((hev c y).mp he)).1, hpc⟩
  · intro c hc
    obtain ⟨x, L, R, _, hL, hR, hp⟩ := (P.members c).mp hc
    refine ⟨L, (hRel c L).mpr ⟨x, L, R, hL, hR, hp, hL⟩, ?_⟩
    intro y hy
    obtain ⟨x', L', R', hL', hR', hp', hy'⟩ := (hRel c y).mp hy
    have he := internal_quine_pair_rows_disjoint P hL hR hL' hR' hp hp'
      ((hp L).mpr (Or.inl rfl)) ((hp L).mpr (Or.inl rfl))
    subst x'
    exact coded_function_value_unique P.leftFunction hy' hL
  · intro c _ y hy
    obtain ⟨x, L, R, hL, _, hp, hy'⟩ := (hRel c y).mp hy
    exact (hp y).mpr (Or.inl (coded_function_value_unique P.leftFunction hy' hL))

theorem internal_quine_pairs_no_supported_swap_system (base : BaseCollection s) {a : U}
    (P : InternalQuinePairs s a) : ¬ Nonempty (PairSwapSystem s P.family) := by
  rintro ⟨S⟩
  exact supported_pair_family_no_choice S (internal_quine_pairs_have_choice base P)

#print axioms internal_quine_pairs_have_choice
#print axioms internal_quine_pairs_no_supported_swap_system
end FullBridge
