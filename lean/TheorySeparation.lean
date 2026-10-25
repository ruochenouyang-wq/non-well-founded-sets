import SolvabilityBridge
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem selfSingleton_decoration (base : BaseCollection s) {a b e : U}
    (ha : SelfSingleton s a) (hb : SelfSingleton s b)
    (he : ∀ x y, CodedRelation s e x y ↔ x = a ∧ y = a) :
    ∃ f, DecorationCode s a e f ∧ CodedRelation s f a b := by
  obtain ⟨p, hp⟩ := orderedPair_exists base.pairing a b
  obtain ⟨f, hf⟩ := base.pairing p p
  have hrel : ∀ x y, CodedRelation s f x y ↔ x = a ∧ y = b := by
    intro x y
    constructor
    · rintro ⟨z, hz, hzxy⟩
      have hzp : z = p := ((hf z).mp hz).elim id id
      subst z
      exact orderedPair_injective hzxy hp
    · rintro ⟨rfl, rfl⟩
      exact ⟨p, (hf p).mpr (Or.inl rfl), hp⟩
  refine ⟨f, ⟨⟨?_, ?_⟩, ?_⟩, (hrel a b).mpr ⟨rfl, rfl⟩⟩
  · intro z hz
    have hzp : z = p := ((hf z).mp hz).elim id id
    subst z
    exact ⟨a, b, (ha a).mpr rfl, hp⟩
  · intro x hx
    have hxa := (ha x).mp hx
    subst x
    exact ⟨b, (hrel a b).mpr ⟨rfl, rfl⟩, fun z hz => ((hrel a z).mp hz).2⟩
  · intro x hx v hxv w
    have hxa := (ha x).mp hx
    have hvb := ((hrel x v).mp hxv).2
    subst x
    subst v
    constructor
    · intro hw
      exact ⟨a, (ha a).mpr rfl, (he a a).mpr ⟨rfl, rfl⟩,
        (hrel a w).mpr ⟨rfl, (hb w).mp hw⟩⟩
    · rintro ⟨y, _, _, hyw⟩
      exact (hb w).mpr ((hrel y w).mp hyw).2

theorem afa_selfSingleton_unique (base : BaseCollection s) (hAFA : AFACode s)
    {a b : U} (ha : SelfSingleton s a) (hb : SelfSingleton s b) : a = b := by
  obtain ⟨e, heG, he⟩ := normalized_relation_comprehension base
    (Formula.equal (n := 2) 0 1) Fin.elim0 a
  have hei : ∀ x y, CodedRelation s e x y ↔ x = a ∧ y = a := by
    intro x y
    have h := he x y
    change CodedRelation s e x y ↔ s x a ∧ s y a ∧ y = x at h
    rw [h, ha x, ha y]
    constructor
    · exact fun h => ⟨h.1, h.2.1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
  obtain ⟨f, hf, hfa⟩ := selfSingleton_decoration base ha ha hei
  obtain ⟨g, hg, hgb⟩ := selfSingleton_decoration base ha hb hei
  obtain ⟨k, _, hu⟩ := hAFA a e heG
  have hfg : f = g := (hu f hf).trans (hu g hg).symm
  rw [hfg] at hfa
  obtain ⟨v, _, hv⟩ := hg.1.2 a ((ha a).mpr rfl)
  exact (hv a hfa).trans (hv b hgb).symm

theorem afa_not_bafa (base : BaseCollection s) (hAFA : AFACode s) : ¬BAFACode s := by
  intro hB
  obtain ⟨a, b, hne, ha, hb⟩ := bafa_distinct_selfSingletons base hB
  exact hne (afa_selfSingleton_unique base hAFA ha hb)

theorem afa_graph_solvability (hAFA : AFACode s) : GraphSolvabilityCode s := by
  intro a e hG
  obtain ⟨f, hf, _⟩ := hAFA a e hG
  exact ⟨f, hf⟩

theorem bafa_quotient_separates (M : BafaChoiceModel.{u}) :
    GraphSolvabilityCode M.behaviorQuotient.mem ∧
      ChoiceCode M.behaviorQuotient.mem ∧ ¬BAFACode M.behaviorQuotient.mem :=
  ⟨afa_graph_solvability M.behaviorQuotient.antiFoundation,
    M.behaviorQuotient.choice,
    afa_not_bafa M.behaviorQuotient.base M.behaviorQuotient.antiFoundation⟩

theorem solvable_non_bafa_model_existence :
    Nonempty SolvableChoiceModel.{u} →
    ∃ M : SolvableChoiceModel.{u}, ¬BAFACode M.mem := by
  rintro ⟨M⟩
  let N := M.behaviorQuotient
  refine ⟨⟨N.Carrier, N.mem, N.base, afa_graph_solvability N.antiFoundation, N.choice⟩, ?_⟩
  exact afa_not_bafa N.base N.antiFoundation

#print axioms afa_not_bafa
#print axioms solvable_non_bafa_model_existence
end FullBridge
