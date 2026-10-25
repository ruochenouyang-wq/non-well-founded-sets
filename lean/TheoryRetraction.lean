import PrunedRoundtrip
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- An external collection of actual finite first-order sentences. -/
def SentenceTheory := Formula 0 → Prop

def SatisfiesTheory (s : U → U → Prop) (T : SentenceTheory) : Prop :=
  ∀ p, T p → Eval s p Fin.elim0

/-- Uniform syntactic image, independent of the model. -/
def behaviorTheory (T : SentenceTheory) : SentenceTheory :=
  fun q => ∃ p, T p ∧ q = behaviorTranslation p

theorem satisfies_behavior_theory (base : BaseCollection s) (T : SentenceTheory) :
    SatisfiesTheory s (behaviorTheory T) ↔ SatisfiesTheory (internalMember base) T := by
  have ht : ∀ p : Formula 0, Eval s (behaviorTranslation p) Fin.elim0 ↔
      Eval (internalMember base) p Fin.elim0 := by
    intro p
    have h := uniform_behavior_translation base p Fin.elim0
    have he : (fun i : Fin 0 => internalCode base (Fin.elim0 i)) = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    rw [he] at h
    exact h
  constructor
  · intro h p hp
    exact (ht p).mp (h _ ⟨p, hp, rfl⟩)
  · rintro h q ⟨p, hp, rfl⟩
    exact (ht p).mpr (h p hp)

theorem pruned_roundtrip_sentence (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hb : SelfSingleton s b) (p : Formula 0) :
    Eval (prunedMember base b) (behaviorTranslation p) Fin.elim0 ↔ Eval s p Fin.elim0 := by
  have ht := uniform_behavior_translation (pruned_quotient_base base ((hb b).mpr rfl)) p Fin.elim0
  have hr := pruned_roundtrip_formula_semantics base hA hb p
    (fun i : Fin 0 => internalCode (pruned_quotient_base base ((hb b).mpr rfl)) (Fin.elim0 i))
  have he : (fun i : Fin 0 => prunedRoundtripMap base hA ((hb b).mpr rfl)
      (internalCode (pruned_quotient_base base ((hb b).mpr rfl)) (Fin.elim0 i))) = Fin.elim0 :=
    funext (fun i => Fin.elim0 i)
  exact ht.trans (he ▸ hr)

theorem pruned_satisfies_behavior_theory (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hb : SelfSingleton s b) (T : SentenceTheory) :
    SatisfiesTheory (prunedMember base b) (behaviorTheory T) ↔ SatisfiesTheory s T := by
  constructor
  · intro h p hp
    exact (pruned_roundtrip_sentence base hA hb p).mp (h _ ⟨p, hp, rfl⟩)
  · rintro h q ⟨p, hp, rfl⟩
    exact (pruned_roundtrip_sentence base hA hb p).mpr (h p hp)

/-- Same-universe model existence, with arbitrary additional sentence axioms.
    No completeness theorem or proof calculus is assumed. -/
theorem afa_bafa_theory_model_existence (T : SentenceTheory) :
    (∃ M : AfaModel.{u}, SatisfiesTheory M.mem T) ↔
      (∃ N : BafaModel.{u}, SatisfiesTheory N.mem (behaviorTheory T)) := by
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨b, hb⟩ := solvability_selfSingleton_exists M.base
      (afa_graph_solvability M.antiFoundation)
    exact ⟨M.prunedBafa b hb, (pruned_satisfies_behavior_theory M.base M.antiFoundation hb T).mpr hM⟩
  · rintro ⟨N, hN⟩
    exact ⟨N.behaviorQuotient, (satisfies_behavior_theory N.base T).mp hN⟩

/-- Semantic consequence in the declared universe, not syntactic derivability. -/
theorem afa_bafa_semantic_consequence (T : SentenceTheory) (p : Formula 0) :
    (∀ M : AfaModel.{u}, SatisfiesTheory M.mem T → Eval M.mem p Fin.elim0) ↔
      (∀ N : BafaModel.{u}, SatisfiesTheory N.mem (behaviorTheory T) →
        Eval N.mem (behaviorTranslation p) Fin.elim0) := by
  constructor
  · intro h N hN
    have ht := h N.behaviorQuotient ((satisfies_behavior_theory N.base T).mp hN)
    exact (bridge_sentence_translation N p).mpr ht
  · intro h M hM
    obtain ⟨b, hb⟩ := solvability_selfSingleton_exists M.base
      (afa_graph_solvability M.antiFoundation)
    exact (pruned_roundtrip_sentence M.base M.antiFoundation hb p).mp
      (h (M.prunedBafa b hb) ((pruned_satisfies_behavior_theory M.base M.antiFoundation hb T).mpr hM))

/-- Both truth values can be realized on one side exactly when they can be
    realized for the translated sentence on the other. This is semantic only. -/
theorem afa_bafa_semantic_independence (T : SentenceTheory) (p : Formula 0) :
    ((∃ M : AfaModel.{u}, SatisfiesTheory M.mem T ∧ Eval M.mem p Fin.elim0) ∧
      (∃ M : AfaModel.{u}, SatisfiesTheory M.mem T ∧ ¬Eval M.mem p Fin.elim0)) ↔
    ((∃ N : BafaModel.{u}, SatisfiesTheory N.mem (behaviorTheory T) ∧
      Eval N.mem (behaviorTranslation p) Fin.elim0) ∧
      (∃ N : BafaModel.{u}, SatisfiesTheory N.mem (behaviorTheory T) ∧
      ¬Eval N.mem (behaviorTranslation p) Fin.elim0)) := by
  have transfer : ∀ P : Prop → Prop,
      (∃ M : AfaModel.{u}, SatisfiesTheory M.mem T ∧ P (Eval M.mem p Fin.elim0)) ↔
      (∃ N : BafaModel.{u}, SatisfiesTheory N.mem (behaviorTheory T) ∧
        P (Eval N.mem (behaviorTranslation p) Fin.elim0)) := by
    intro P
    constructor
    · rintro ⟨M, hM, hp⟩
      obtain ⟨b, hb⟩ := solvability_selfSingleton_exists M.base
        (afa_graph_solvability M.antiFoundation)
      refine ⟨M.prunedBafa b hb,
        (pruned_satisfies_behavior_theory M.base M.antiFoundation hb T).mpr hM, ?_⟩
      exact (propext (pruned_roundtrip_sentence M.base M.antiFoundation hb p)).symm ▸ hp
    · rintro ⟨N, hN, hp⟩
      exact ⟨N.behaviorQuotient, (satisfies_behavior_theory N.base T).mp hN,
        propext (bridge_sentence_translation N p) ▸ hp⟩
  exact and_congr (transfer id) (transfer Not)

structure AfaNoChoiceModel extends AfaModel.{u} where
  notChoice : ¬ChoiceCode mem

structure BafaNoChoiceModel extends BafaModel.{u} where
  notChoice : ¬ChoiceCode mem

def AfaNoChoiceModel.prunedBafa (M : AfaNoChoiceModel.{u}) (b : M.Carrier)
    (hb : SelfSingleton M.mem b) : BafaNoChoiceModel.{u} where
  toBafaModel := M.toAfaModel.prunedBafa b hb
  notChoice := fun h => M.notChoice ((pruned_afa_choice_iff M.base M.antiFoundation hb).mp h)

theorem afa_to_bafa_no_choice_model_existence :
    Nonempty AfaNoChoiceModel.{u} → Nonempty BafaNoChoiceModel.{u} := by
  rintro ⟨M⟩
  obtain ⟨b, hb⟩ := solvability_selfSingleton_exists M.base (afa_graph_solvability M.antiFoundation)
  exact ⟨M.prunedBafa b hb⟩

/-- The reverse condition explicitly concerns the quotient's failure of AC;
    source failure alone is not substituted for it. -/
theorem afa_no_choice_iff_bafa_quotient_no_choice :
    Nonempty AfaNoChoiceModel.{u} ↔
      ∃ N : BafaNoChoiceModel.{u}, ¬ChoiceCode N.toBafaModel.behaviorQuotient.mem := by
  constructor
  · rintro ⟨M⟩
    obtain ⟨b, hb⟩ := solvability_selfSingleton_exists M.base (afa_graph_solvability M.antiFoundation)
    refine ⟨M.prunedBafa b hb, ?_⟩
    intro h
    have hv := (pruned_roundtrip_formula_semantics M.base M.antiFoundation hb choiceSentence Fin.elim0).mp
      ((eval_choiceSentence _).mpr h)
    have he : (fun i : Fin 0 => prunedRoundtripMap M.base M.antiFoundation ((hb b).mpr rfl)
        (Fin.elim0 i)) = Fin.elim0 := funext (fun i => Fin.elim0 i)
    exact M.notChoice ((eval_choiceSentence _).mp (he ▸ hv))
  · rintro ⟨N, hN⟩
    exact ⟨⟨N.toBafaModel.behaviorQuotient, hN⟩⟩

#print axioms afa_bafa_semantic_consequence
#print axioms afa_bafa_semantic_independence
#print axioms afa_no_choice_iff_bafa_quotient_no_choice
end FullBridge
