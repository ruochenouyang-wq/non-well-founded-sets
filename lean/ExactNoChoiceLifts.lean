import CompleteChoiceSeparation
namespace FullBridge
universe u

/-- Every externally countable complete AFA model has a complete BAFA
    preimage failing object Choice, with precisely the original behavior model.
    Neither object Choice nor its negation is required of the AFA input. -/
theorem countable_afa_exact_no_choice_lift (M : AfaModel.{u})
    (enum : Nat → M.Carrier) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧
      ∃ F : N.behaviorQuotient.Carrier → M.Carrier,
        (∀ X Y, F X = F Y → X = Y) ∧ (∀ y, ∃ X, F X = y) ∧
        (∀ X Y, N.behaviorQuotient.mem X Y ↔ M.mem (F X) (F Y)) ∧
        ElementaryMap N.behaviorQuotient.mem M.mem F := by
  obtain ⟨b, hb⟩ := solvability_selfSingleton_exists M.base (afa_graph_solvability M.antiFoundation)
  let P := M.prunedBafa b hb
  let ep : Nat → P.Carrier := fun n => prunedCode M.base b (enum n)
  have hep : ∀ X : P.Carrier, ∃ n, ep n = X := by
    intro X
    obtain ⟨x, rfl⟩ := least_global_code_onto M.base prunedMemberFormula
      (cons b Fin.elim0) (pruned_edges_are_members b) X
    obtain ⟨n, hn⟩ := henum x
    exact ⟨n, congrArg (prunedCode M.base b) hn⟩
  obtain ⟨z, w, hw, J, ctx, hbase, hB, hnc, _⟩ :=
    countable_bafa_full_no_choice_model P.base P.boffa ep hep
  let N : BafaModel.{u} := ⟨CoveredMaskCarrier P.mem w J, coveredMaskMember J, hbase, hB⟩
  let q := coveredQuotientMap P.base hbase
  let r := prunedRoundtripMap M.base M.antiFoundation ((hb b).mpr rfl)
  let F : N.behaviorQuotient.Carrier → M.Carrier := fun X => r (q X)
  have hqi := covered_quotient_map_injective P.base hw ctx hbase
  have hqo := covered_quotient_map_surjective P.base hw ctx hbase
  have hqm := covered_quotient_map_members P.base hw ctx hbase
  have hri := pruned_roundtrip_injective M.base M.antiFoundation ((hb b).mpr rfl)
  have hro := pruned_roundtrip_surjective M.base M.antiFoundation hb
  have hrm := pruned_roundtrip_members M.base M.antiFoundation ((hb b).mpr rfl)
  have hFi : ∀ X Y, F X = F Y → X = Y := fun X Y h => hqi X Y (hri (q X) (q Y) h)
  have hFo : ∀ y, ∃ X, F X = y := by
    intro y
    obtain ⟨Z, hZ⟩ := hro y
    obtain ⟨X, hX⟩ := hqo Z
    exact ⟨X, (congrArg r hX).trans hZ⟩
  have hFm : ∀ X Y, N.behaviorQuotient.mem X Y ↔ M.mem (F X) (F Y) :=
    fun X Y => (hqm X Y).trans (hrm (q X) (q Y))
  exact ⟨N, hnc, F, hFi, hFo, hFm, fun p v => eval_bijective_members F hFi hFo hFm p v⟩

/-- Arbitrary additional target sentences are retained by the no-choice lift.
    This is a semantic model transfer with an explicit external enumeration,
    not a syntactic consistency or completeness theorem. -/
theorem countable_afa_theory_no_choice_lift (M : AfaModel.{u})
    (enum : Nat → M.Carrier) (henum : ∀ x, ∃ n, enum n = x)
    (T : SentenceTheory) (hT : SatisfiesTheory M.mem T) :
    ∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧
      SatisfiesTheory N.behaviorQuotient.mem T ∧ SatisfiesTheory N.mem (behaviorTheory T) := by
  obtain ⟨N, hnc, F, _, _, _, hF⟩ := countable_afa_exact_no_choice_lift M enum henum
  have hNT : SatisfiesTheory N.behaviorQuotient.mem T := by
    intro p hp
    have h := hF p Fin.elim0
    have he : (fun i : Fin 0 => F (Fin.elim0 i)) = Fin.elim0 := funext (fun i => Fin.elim0 i)
    rw [he] at h
    exact h.mpr (hT p hp)
  exact ⟨N, hnc, hNT, (satisfies_behavior_theory N.base T).mpr hNT⟩

#print axioms countable_afa_exact_no_choice_lift
#print axioms countable_afa_theory_no_choice_lift
end FullBridge
