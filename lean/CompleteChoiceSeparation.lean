import CoveredQuotientComparison
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Source choice passes to the ambient behavior quotient and then, via
    the proved quotient isomorphism, to the quotient of the covered model. -/
theorem covered_quotient_inherits_ambient_choice (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (ctx : UniversalActionContext base J) (hbase : BaseCollection (coveredMaskMember J))
    (hAC : ChoiceCode s) : ChoiceCode (internalMember hbase) :=
  (covered_quotient_choice_iff base hw ctx hbase).mpr (internal_choice base hAC)

/-- Conditional full-model choice separation: an externally countable
    BaseCollection+BAFA+AC model yields a BaseCollection+BAFA model without
    choice whose complete AFA behavior quotient satisfies choice.
    The conclusion is not unconditional model existence. -/
theorem countable_bafa_full_choice_separation (base : BaseCollection s) (hB : BAFACode s)
    (hAC : ChoiceCode s) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ M : BafaModel.{u}, ¬ChoiceCode M.mem ∧ Replacement M.mem ∧
      BaseCollection M.behaviorQuotient.mem ∧ AFACode M.behaviorQuotient.mem ∧
      ChoiceCode M.behaviorQuotient.mem ∧ Replacement M.behaviorQuotient.mem := by
  obtain ⟨z, w, hw, J, ctx, hbase, hbafa, hnc, _⟩ :=
    countable_bafa_full_no_choice_model base hB enum henum
  let M : BafaModel.{u} := ⟨CoveredMaskCarrier s w J, coveredMaskMember J, hbase, hbafa⟩
  exact ⟨M, hnc, collection_separation_replacement _ hbase.collection hbase.separation,
    M.behaviorQuotient.base, M.behaviorQuotient.antiFoundation,
    covered_quotient_inherits_ambient_choice base hw ctx hbase hAC, bridge_target_replacement M⟩

#print axioms covered_quotient_inherits_ambient_choice
#print axioms countable_bafa_full_choice_separation
end FullBridge
