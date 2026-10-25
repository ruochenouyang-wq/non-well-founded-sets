# Results and Proof Entry Points

All statements below refer to the definitions in the Lean sources. Model-existence conclusions require the stated input models. The formalizations are over Type universes, not a separate syntactic proof calculus.

## Model existence under translation

B plus AFA models of T exist exactly when B plus BAFA models of its behavior translation exist. Same-universe semantic model existence.

Proof: [`afa_bafa_theory_model_existence`](../lean/TheoryRetraction.lean#L54).

## Semantic consequence

Consequence transfers for translated sentences; no proof calculus or syntactic completeness is assumed.

Proof: [`afa_bafa_semantic_consequence`](../lean/TheoryRetraction.lean#L66).

## Exact no-choice lift

Given a full AFA model with a surjective external Nat enumeration, construct a full BAFA model failing AC with an isomorphic behavior quotient.

Proof: [`countable_afa_exact_no_choice_lift`](../lean/ExactNoChoiceLifts.lean#L8).

## Arbitrary input

Given any full AFA model and a Nat-indexed parameter sequence, construct a full BAFA source failing AC whose quotient embeds elementarily into the input and covers the parameters. No surjectivity claim.

Proof: [`afa_no_choice_elementary_lift_with_parameters`](../lean/UnrestrictedNoChoiceTransfer.lean#L21).

## Behavior conservativity

Adding failure of object choice does not change the displayed semantic consequence relation in the behavior fragment, over translated theories.

Proof: [`bafa_no_choice_behavior_consequence`](../lean/UnrestrictedNoChoiceTransfer.lean#L105).

## Choice decomposition

Under BaseCollection, source choice is equivalent to target choice and fiber choice.

Proof: [`source_choice_iff_target_and_fiber`](../lean/FiberChoice.lean#L181).

## Full fiber choice

Under BaseCollection plus BAFA, fiber choice is equivalent to AC.

Proof: [`bafa_fiber_choice_iff_choice`](../lean/BafaFiberChoice.lean#L144).

## Homogeneous pair choice

Under BaseCollection plus BAFA, FC2 is equivalent to AC2.

Proof: [`bafa_fiber_pair_choice_iff_pair_choice`](../lean/BafaPairChoice.lean#L63).

## Self-singleton pair choice

Under BaseCollection plus BAFA, QC2 is equivalent to AC2.

Proof: [`bafa_quine_pair_choice_iff_pair_choice`](../lean/BafaPairChoice.lean#L69).

## AFA boundary

Under BaseCollection plus AFA, FC2 holds because no homogeneous pair of distinct elements exists.

Proof: [`afa_fiber_pair_choice`](../lean/AfaPairChoiceBoundary.lean#L21).

## Pair-choice failure

Given an externally countable full BAFA model, construct a full BAFA model failing AC2, FC2 and QC2.

Proof: [`countable_bafa_pair_choice_complete_bridge`](../lean/CoveredPairChoiceFailure.lean#L77).

## Choice across the quotient

If the given externally countable full BAFA source also satisfies AC, the constructed model fails AC2 while its quotient satisfies AC and AC2.

Proof: [`countable_bafa_pair_choice_separation`](../lean/CoveredPairChoiceFailure.lean#L91).

## Counting boundary

In every full BAFA model, the property of having at least two distinct members is not definable by a pure ordinary modal formula.

Proof: [`bafa_two_members_not_pure_modal`](../lean/ModalCountingBoundary.lean#L70).

## Quotient factorization

Under BaseCollection, an explicit coequalizer property holds for the displayed internal behavior kernel projections and exact-member maps.

Proof: [`internal_quotient_coequalizer`](../lean/MemberCoalgebraMaps.lean#L118).

## Predicate descent

Under BaseCollection, external predicates descend exactly when internally behavior-invariant. This is not internal definability of all such predicates.

Proof: [`internal_predicate_descent_iff`](../lean/ModalPredicateDescent.lean#L63).

## Raw versus translated choice

Given an externally countable full BAFA model, construct a full BAFA model falsifying raw FC2 but satisfying its behavior translation.

Proof: [`countable_bafa_pair_choice_translation_boundary`](../lean/PairChoiceScreening.lean#L14).
