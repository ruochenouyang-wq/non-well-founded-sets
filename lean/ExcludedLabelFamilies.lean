import PrunedTaggedLoops
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def ExcludedLabel (s : U → U → Prop) (b tag x l : U) : Prop :=
  ∃ p, IsOrderedPair s p tag x ∧ IsPair s l b p

def excludedLabelFormula {n} (b tag x l : Fin n) : Formula n :=
  .ex (.conj (orderedPairFormula 0 tag.succ x.succ) (pairFormula l.succ b.succ 0))

theorem eval_excludedLabelFormula {n} (b tag x l : Fin n) (e : Fin n → U) :
    Eval s (excludedLabelFormula b tag x l) e ↔ ExcludedLabel s (e b) (e tag) (e x) (e l) := by
  simp only [excludedLabelFormula, Eval, eval_orderedPairFormula, eval_pairFormula, ExcludedLabel, cons_succ]
  rfl

theorem excluded_label_total (base : BaseCollection s) (b tag x : U) :
    ∃ l, ExcludedLabel s b tag x l := by
  obtain ⟨p, hp⟩ := orderedPair_exists base.pairing tag x
  obtain ⟨l, hl⟩ := base.pairing b p
  exact ⟨l, p, hp, hl⟩

theorem excluded_label_unique (base : BaseCollection s) {b tag x l m : U}
    (hl : ExcludedLabel s b tag x l) (hm : ExcludedLabel s b tag x m) : l = m := by
  obtain ⟨p, hp, hl⟩ := hl
  obtain ⟨q, hq, hm⟩ := hm
  have hqp := orderedPair_unique base.extensional hq hp
  subst q
  exact pair_unique base.extensional hl hm

theorem excluded_label_injective {b tag x y l : U}
    (hne : ∀ p z, IsOrderedPair s p tag z → p ≠ b)
    (hx : ExcludedLabel s b tag x l) (hy : ExcludedLabel s b tag y l) : x = y := by
  obtain ⟨p, hp, hl⟩ := hx
  obtain ⟨q, hq, hm⟩ := hy
  have hpq := (hm p).mp ((hl p).mpr (Or.inr rfl))
  rcases hpq with hpb | hpq
  · exact False.elim (hne p x hp hpb)
  · subst q
    exact (orderedPair_injective hp hq).2

/-- A total internally coded injective family of excluded labels, avoiding any
    prescribed source set. The family exists without object-level Choice. -/
theorem excluded_label_family (base : BaseCollection s) {b : U} (hb : SelfSingleton s b) (a t : U) :
    ∃ L f, FunctionCode s a f ∧ InjectiveCode s f ∧ RangeCode s a f L ∧
      ∀ l, s l L → s b l ∧ l ≠ b ∧ ¬s l t := by
  obtain ⟨d, hd, htd⟩ := transitive_cover_exists base t
  obtain ⟨one, hone⟩ := base.pairing b b
  obtain ⟨bound, hbound⟩ := binary_union_exists base.pairing base.union d one
  obtain ⟨tag, htag⟩ := fresh_orderedPair_tag base bound
  have hpb : ∀ p x, IsOrderedPair s p tag x → p ≠ b := by
    intro p x hp heq
    subst p
    exact htag x b hp ((hbound b).mpr (Or.inr ((hone b).mpr (Or.inl rfl))))
  have hpd : ∀ p x, IsOrderedPair s p tag x → ¬s p d :=
    fun p x hp h => htag x p hp ((hbound p).mpr (Or.inl h))
  obtain ⟨L, hL⟩ := collection_separation_replacement s base.collection base.separation 2
    (excludedLabelFormula 2 3 1 0) (cons b (cons tag Fin.elim0)) a (by
      intro x _
      obtain ⟨l, hl⟩ := excluded_label_total base b tag x
      refine ⟨l, (eval_excludedLabelFormula 2 3 1 0 _).mpr hl, ?_⟩
      intro z hz
      exact excluded_label_unique base ((eval_excludedLabelFormula 2 3 1 0 _).mp hz) hl)
  have hL' : ∀ l, s l L ↔ ∃ x, s x a ∧ ExcludedLabel s b tag x l := by
    intro l
    have h := hL l
    simp only [eval_excludedLabelFormula] at h
    exact h
  obtain ⟨u, hu⟩ := binary_union_exists base.pairing base.union a L
  obtain ⟨f, hfmem⟩ := relation_comprehension_members base
    (.conj (.member 1 2) (excludedLabelFormula 3 4 1 0)) (cons a (cons b (cons tag Fin.elim0))) u
  have hf' : ∀ x l, CodedRelation s f x l ↔ s x a ∧ ExcludedLabel s b tag x l := by
    intro x l
    constructor
    · rintro ⟨p, hp, hpxl⟩
      obtain ⟨x', l', _, _, hp', hev⟩ := (hfmem p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxl hp'
      exact ⟨hev.1, (eval_excludedLabelFormula 3 4 1 0 _).mp hev.2⟩
    · rintro ⟨hx, hl⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x l
      exact ⟨p, (hfmem p).mpr ⟨x, l, (hu x).mpr (Or.inl hx),
        (hu l).mpr (Or.inr ((hL' l).mpr ⟨x, hx, hl⟩)), hp,
        hx, (eval_excludedLabelFormula 3 4 1 0 _).mpr hl⟩, hp⟩
  refine ⟨L, f, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, l, _, _, hpair, hev⟩ := (hfmem p).mp hp
    exact ⟨x, l, hev.1, hpair⟩
  · intro x hx
    obtain ⟨l, hl⟩ := excluded_label_total base b tag x
    refine ⟨l, (hf' x l).mpr ⟨hx, hl⟩, ?_⟩
    intro z hz
    exact excluded_label_unique base ((hf' x z).mp hz).2 hl
  · intro x y l hx hy
    exact excluded_label_injective hpb ((hf' x l).mp hx).2 ((hf' y l).mp hy).2
  · intro l
    exact (hL' l).trans ⟨fun ⟨x, hx, hl⟩ => ⟨x, hx, (hf' x l).mpr ⟨hx, hl⟩⟩,
      fun ⟨x, hx, hxl⟩ => ⟨x, hx, ((hf' x l).mp hxl).2⟩⟩
  · intro l hl
    obtain ⟨x, _, p, hp, hpair⟩ := (hL' l).mp hl
    refine ⟨(hpair b).mpr (Or.inl rfl), ?_, ?_⟩
    · intro hlb
      exact hpb p x hp ((hb p).mp (hlb ▸ (hpair p).mpr (Or.inr rfl)))
    · intro hlt
      exact hpd p x hp (hd l (htd l hlt) p ((hpair p).mpr (Or.inr rfl)))

#print axioms excluded_label_family
end FullBridge
