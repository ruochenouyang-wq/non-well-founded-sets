import CountableAfaModels
import ExactNoChoiceLifts

namespace FullBridge
universe u v

/-- Elementary maps agree on arbitrary collections of actual finite sentences. -/
theorem elementary_map_satisfies_theory {U : Type u} {V : Type v}
    {s : U → U → Prop} {t : V → V → Prop} {j : U → V}
    (hj : ElementaryMap s t j) (T : SentenceTheory) :
    SatisfiesTheory s T ↔ SatisfiesTheory t T := by
  constructor
  · intro h p hp
    exact (elementary_map_sentence hj p).mp (h p hp)
  · intro h p hp
    exact (elementary_map_sentence hj p).mpr (h p hp)

/-- Arbitrarily large AFA targets have a no-choice BAFA model whose behavior
    quotient embeds elementarily into the target and covers prescribed countable
    parameters. Surjectivity onto the original target is not asserted. -/
theorem afa_no_choice_elementary_lift_with_parameters (M : AfaModel.{u})
    (seed : Nat → M.Carrier) :
    ∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧
      ∃ j : N.behaviorQuotient.Carrier → M.Carrier,
        ElementaryMap N.behaviorQuotient.mem M.mem j ∧
        (∀ k, ∃ X, j X = seed k) := by
  obtain ⟨C, enum, honto, i, hi, hseed⟩ :=
    countable_afa_elementary_model_with_parameters M seed
  obtain ⟨N, hnc, F, _, hFonto, _, hF⟩ := countable_afa_exact_no_choice_lift C enum honto
  refine ⟨N, hnc, fun X => i (F X), elementary_map_comp hF hi, ?_⟩
  intro k
  obtain ⟨c, hc⟩ := hseed k
  obtain ⟨X, hX⟩ := hFonto c
  exact ⟨X, (congrArg i hX).trans hc⟩

/-- No external-countability or object-Choice assumption on the input model. -/
theorem afa_no_choice_elementary_lift (M : AfaModel.{u}) :
    ∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧
      ∃ j : N.behaviorQuotient.Carrier → M.Carrier,
        ElementaryMap N.behaviorQuotient.mem M.mem j := by
  obtain ⟨z, _⟩ := M.base.empty
  obtain ⟨N, hnc, j, hj, _⟩ :=
    afa_no_choice_elementary_lift_with_parameters M (fun _ => z)
  exact ⟨N, hnc, j, hj⟩

/-- Every target sentence theory has a full no-choice preimage at the level of
    satisfaction; its behavior quotient satisfies the prescribed target theory. -/
theorem afa_theory_no_choice_lift (M : AfaModel.{u})
    (T : SentenceTheory) (hT : SatisfiesTheory M.mem T) :
    ∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧
      SatisfiesTheory N.behaviorQuotient.mem T ∧
      SatisfiesTheory N.mem (behaviorTheory T) := by
  obtain ⟨N, hnc, j, hj⟩ := afa_no_choice_elementary_lift M
  have hNT := (elementary_map_satisfies_theory hj T).mpr hT
  exact ⟨N, hnc, hNT, (satisfies_behavior_theory N.base T).mpr hNT⟩

/-- Conditional, same-universe semantic model existence. No completeness or
    proof calculus, and no enumeration of a source carrier, is assumed. -/
theorem afa_no_choice_theory_model_existence (T : SentenceTheory) :
    (∃ M : AfaModel.{u}, SatisfiesTheory M.mem T) ↔
      (∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧
        SatisfiesTheory N.mem (behaviorTheory T)) := by
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨N, hnc, _, hN⟩ := afa_theory_no_choice_lift M T hM
    exact ⟨N, hnc, hN⟩
  · rintro ⟨N, _, hN⟩
    exact ⟨N.behaviorQuotient, (satisfies_behavior_theory N.base T).mp hN⟩

theorem afa_no_choice_model_existence_iff :
    Nonempty AfaModel.{u} ↔ Nonempty BafaNoChoiceModel.{u} := by
  constructor
  · rintro ⟨M⟩
    obtain ⟨N, hnc, _⟩ := afa_no_choice_elementary_lift M
    exact ⟨⟨N, hnc⟩⟩
  · rintro ⟨N⟩
    exact ⟨N.toBafaModel.behaviorQuotient⟩

/-- Choice failure can be imposed on a BAFA source without changing the
    satisfiability of any theory in the behavior-translated language. -/
theorem bafa_no_choice_behavior_satisfiability (T : SentenceTheory) :
    (∃ N : BafaModel.{u}, SatisfiesTheory N.mem (behaviorTheory T)) ↔
      (∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧
        SatisfiesTheory N.mem (behaviorTheory T)) :=
  (afa_bafa_theory_model_existence T).symm.trans (afa_no_choice_theory_model_existence T)

/-- Semantic consequence, quantified over all full no-choice BAFA models. -/
theorem afa_no_choice_semantic_consequence (T : SentenceTheory) (p : Formula 0) :
    (∀ M : AfaModel.{u}, SatisfiesTheory M.mem T → Eval M.mem p Fin.elim0) ↔
      (∀ N : BafaModel.{u}, ¬ChoiceCode N.mem →
        SatisfiesTheory N.mem (behaviorTheory T) →
        Eval N.mem (behaviorTranslation p) Fin.elim0) := by
  constructor
  · intro h N _ hN
    apply (bridge_sentence_translation N p).mpr
    exact h N.behaviorQuotient ((satisfies_behavior_theory N.base T).mp hN)
  · intro h M hM
    obtain ⟨N, hnc, j, hj⟩ := afa_no_choice_elementary_lift M
    have hNT := (elementary_map_satisfies_theory hj T).mpr hM
    have hp := h N hnc ((satisfies_behavior_theory N.base T).mpr hNT)
    exact (elementary_map_sentence hj p).mp ((bridge_sentence_translation N p).mp hp)

/-- Adding not-Choice is semantically conservative for the behavior fragment
    over BAFA plus any behavior-translated theory. This is not a syntactic claim. -/
theorem bafa_no_choice_behavior_consequence (T : SentenceTheory) (p : Formula 0) :
    (∀ N : BafaModel.{u}, SatisfiesTheory N.mem (behaviorTheory T) →
      Eval N.mem (behaviorTranslation p) Fin.elim0) ↔
    (∀ N : BafaModel.{u}, ¬ChoiceCode N.mem →
      SatisfiesTheory N.mem (behaviorTheory T) →
      Eval N.mem (behaviorTranslation p) Fin.elim0) :=
  (afa_bafa_semantic_consequence T p).symm.trans (afa_no_choice_semantic_consequence T p)

/-- Both sentence truth values transfer, so semantic independence is preserved. -/
theorem afa_no_choice_semantic_independence (T : SentenceTheory) (p : Formula 0) :
    ((∃ M : AfaModel.{u}, SatisfiesTheory M.mem T ∧ Eval M.mem p Fin.elim0) ∧
      (∃ M : AfaModel.{u}, SatisfiesTheory M.mem T ∧ ¬Eval M.mem p Fin.elim0)) ↔
    ((∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧
        SatisfiesTheory N.mem (behaviorTheory T) ∧ Eval N.mem (behaviorTranslation p) Fin.elim0) ∧
      (∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧
        SatisfiesTheory N.mem (behaviorTheory T) ∧ ¬Eval N.mem (behaviorTranslation p) Fin.elim0)) := by
  have transfer : ∀ P : Prop → Prop,
      (∃ M : AfaModel.{u}, SatisfiesTheory M.mem T ∧ P (Eval M.mem p Fin.elim0)) ↔
      (∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧ SatisfiesTheory N.mem (behaviorTheory T) ∧
        P (Eval N.mem (behaviorTranslation p) Fin.elim0)) := by
    intro P
    constructor
    · rintro ⟨M, hM, hp⟩
      obtain ⟨N, hnc, j, hj⟩ := afa_no_choice_elementary_lift M
      have hNT := (elementary_map_satisfies_theory hj T).mpr hM
      have he := (bridge_sentence_translation N p).trans (elementary_map_sentence hj p)
      exact ⟨N, hnc, (satisfies_behavior_theory N.base T).mpr hNT, (propext he).symm ▸ hp⟩
    · rintro ⟨N, _, hN, hp⟩
      exact ⟨N.behaviorQuotient, (satisfies_behavior_theory N.base T).mp hN,
        propext (bridge_sentence_translation N p) ▸ hp⟩
  exact and_congr (transfer id) (transfer Not)

/-- Object Choice remains a property of the behavior target, independent of
    the constructed source's failure of Choice. -/
theorem afa_choice_preserving_no_choice_lift (M : AfaModel.{u}) :
    ∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧
      (ChoiceCode N.behaviorQuotient.mem ↔ ChoiceCode M.mem) := by
  obtain ⟨N, hnc, j, hj⟩ := afa_no_choice_elementary_lift M
  exact ⟨N, hnc, elementary_map_choice_iff hj⟩

/-- Full choice separation without a countability assumption on the source. -/
theorem bafa_full_choice_separation (M : BafaChoiceModel.{u}) :
    ∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧ Replacement N.mem ∧
      BaseCollection N.behaviorQuotient.mem ∧ AFACode N.behaviorQuotient.mem ∧
      ChoiceCode N.behaviorQuotient.mem ∧ Replacement N.behaviorQuotient.mem := by
  obtain ⟨N, hnc, hchoice⟩ := afa_choice_preserving_no_choice_lift M.toBafaModel.behaviorQuotient
  exact ⟨N, hnc, collection_separation_replacement _ N.base.collection N.base.separation,
    N.behaviorQuotient.base, N.behaviorQuotient.antiFoundation,
    hchoice.mpr (internal_choice M.base M.choice), bridge_target_replacement N⟩

#print axioms afa_no_choice_elementary_lift_with_parameters
#print axioms afa_no_choice_theory_model_existence
#print axioms bafa_no_choice_behavior_consequence
#print axioms bafa_full_choice_separation
end FullBridge
