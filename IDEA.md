# What Does a Behavior Quotient Forget About Sets?

## The question

Two sets can have matching membership behavior while retaining different identities in a non-well-founded universe. What remains of set theory when these identities are identified? Can the resulting behavior model retain choice even when its source does not?

This project studies those questions through complete model constructions. Its main object is a bridge from Boffa-style anti-foundation (BAFA) to Aczel-style anti-foundation (AFA), together with explicit tests of what the bridge preserves and forgets.

## The setting

Write B for the project's `BaseCollection` theory: Extensionality, Empty Set, Pairing, Union, Power Set, Infinity, and the Separation and Collection schemes over actual finite first-order formulas. Replacement follows from the schemes. Neither Choice nor Foundation is built into B.

Write Q(N) for the internal behavior quotient of a BAFA model N. The equivalence relation uses a relation coded by a set of the model, augmented by identity, to witness bisimulation. This restriction matters: arbitrary external relations are not substituted for internal witnesses.

The associated formula translation changes the interpretation of both equality and membership. Statements about translated formulas must therefore be distinguished from statements about the original formulas.

## The model construction

The quotient Q(N) satisfies B and AFA. A reverse construction gives, for every additional sentence theory T, an equivalence between the existence of an AFA model of T and a BAFA model of its behavior translation. Semantic consequence also transfers under that translation, in the declared Lean universe.

A stronger construction supplies sources without choice. For every given externally countable full AFA model M, there is a full BAFA model N failing object-level AC such that Q(N) is isomorphic to M. The countability assumption is external and explicit; M need not assume AC or its negation.

For arbitrary AFA inputs, the proved conclusion is an elementary embedding Q(N) into M that covers a prescribed countable parameter sequence. It is not asserted to be onto M. This gives a corresponding semantic conservativity result for the behavior-translated fragment when failure of choice is imposed on the source.

The construction verifies the whole base, including Power Set and full Separation and Collection. Closure under a small list of set operations would not suffice for this conclusion.

## Why identity matters for choice

The project defines fiber choice for internal families of nonempty sets whose members, within each set, have the same internal behavior. Over B, source choice is equivalent to the conjunction of quotient choice and fiber choice. Under B plus BAFA, fiber choice itself is equivalent to full AC.

A smaller candidate restricts each member of the family to exactly two distinct elements:

- AC2: choice for arbitrary internal families of two-element sets.
- FC2: the same requirement restricted to behavior-homogeneous pairs.
- QC2: the same requirement restricted to pairs of self-singletons, where a self-singleton x satisfies x = {x}.

Under B plus BAFA, AC2, FC2, and QC2 are equivalent. The reduction takes the union of an arbitrary pair family, realizes a single internal injection from that union into distinct self-singletons, forms the image family, and pulls a choice function back. It does not assume a simultaneous left/right orientation of the input pairs.

This classifies the candidate rather than producing a new axiom strength. Under AFA, behavior equivalence implies equality, so no behavior-homogeneous pair of distinct elements exists; FC2 and QC2 hold vacuously. This observation alone says nothing about whether AC2 holds in an AFA model.

Given an externally countable B plus BAFA source model, the supported-model construction yields a full BAFA model in which all three pair-choice principles fail. With the additional assumption of AC in the given source, the constructed model can fail AC2 while its AFA behavior quotient satisfies full AC. This compares different models; it is not a separation of AC2 from AC within a single BAFA model.

## What can be observed after quotienting

The formalization connects the quotient to exact-member maps, an explicit coequalizer universal property, and ordinary modal invariance. Predicates pulled back from the quotient are exactly the external predicates invariant under internal behavior. This is an external predicate result, not a Separation scheme for arbitrary external predicates.

In a full BAFA model there are objects with the same pure ordinary modal theory but different truth values for having at least two distinct members. The counting property therefore cannot be defined in that pure modal language. No converse from modal equivalence to bisimilarity, or claim of final coalgebra structure, is made.

A further boundary occurs at the sentence level: conditionally constructed full BAFA models can falsify the original FC2 sentence while satisfying its behavior translation. Translating an identity-sensitive demand changes the demand.

## What remains worth investigating

The most substantial result to assess against prior work is the construction of complete sources without choice that retain a prescribed behavior theory. The model bridge, quotient factorization, and symmetric choice obstructions should be compared with their established antecedents before any priority claim.

Open directions include an exact no-choice lift for arbitrary-size AFA targets, a separate comparison of AC2 with full AC over the chosen base, and identity requirements that resist the uniform encoding reduction above. These are questions, not additional verified conclusions.

The intended contribution of this repository is an inspectable idea and its formal evidence. The current work establishes neither a new-strength axiom nor historical originality.
