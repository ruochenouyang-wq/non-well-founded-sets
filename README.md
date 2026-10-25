# Identity and Behavior in Non-Well-Founded Sets

A research idea with Lean-checked proofs: compare complete models of non-well-founded set theory by identifying sets with the same internally witnessed membership behavior, and study what this identification forgets about identity and choice.

Start with [the idea](IDEA.md). This is an exploratory formalization and a collection of verified results, not a claim of a new axiom or established mathematical priority.

## Main results

- **A model bridge.** A behavior quotient sends a model of the base theory plus BAFA to a model of the base theory plus AFA. A reverse construction yields a correspondence of model existence and semantic consequence under a uniform translation of formulas.
- **Sources without choice.** Every given externally countable AFA model has a full BAFA source failing object-level choice whose behavior quotient is isomorphic to the input. For arbitrary AFA inputs, the established result provides an elementary embedding of the quotient into the input, covering any prescribed countable sequence of parameters.
- **Identity-sensitive boundaries.** Choice decomposes into quotient choice and fiber choice. Under BAFA, choice for behavior-homogeneous pairs and choice for pairs of self-singletons are each equivalent to ordinary choice for pairs. Pure ordinary modal formulas cannot express the demonstrated branching-count distinction.

The base theory includes Extensionality, Empty Set, Pairing, Union, Power Set, Infinity, and full first-order Separation and Collection. It does not assume object-level Choice or Foundation. Behavior in the bridge is internally coded; it is not silently identified with arbitrary external bisimilarity.

Precise hypotheses and proof entry points are in the [result map](docs/results.md). In particular, model constructions are conditional on given models; they are not unconditional existence proofs or formalized syntactic consistency statements.

## Reproduce the verification

Requirements: Python 3 and Lean **4.33.1**, normally installed through elan. The toolchain is pinned in `lean-toolchain`. The Lean sources use the bundled `Std` library and do not require mathlib or Python packages.

From the repository root, run:

```sh
python3 lean/verify.py
```

The script compiles all 340 modules in a fresh temporary directory, then imports `PairChoiceScreening` and checks the axiom dependencies of all 1,656 named theorems. It writes `verification/proof-manifest.json` and `verification/lean-verification.txt`. Success is reported only after both compilation and the dependency audit pass.

The permitted Lean foundational dependencies are `propext`, `Classical.choice`, and `Quot.sound`. Metatheoretic `Classical.choice` is distinct from the object-model property `ChoiceCode`. The number of named theorems includes helper lemmas and formula-evaluation results; it is not a count of original discoveries.

## Repository contents

- [IDEA.md](IDEA.md): motivation, construction, interpretation, and open questions.
- [docs/results.md](docs/results.md): mathematical statements linked to Lean declarations.
- [docs/references.md](docs/references.md): literature context and unresolved comparisons.
- [docs/review.md](docs/review.md): publication-content review and verification scope.
- `lean/`: all proof sources and the clean verification script.
- `verification/`: source provenance, verification output, and content-audit records.

## Provenance and feedback

The research exploration, Lean implementation, and documentation were developed with substantial assistance from OpenAI Codex. Kernel checking establishes derivability of the encoded statements; it does not establish that every definition captures its intended informal concept, that a result is historically new, or that the exposition has received independent expert review.

Useful feedback would identify a precise mismatch between a definition and its intended meaning, a relevant prior result, or a meaningful strengthening of one of the stated theorems. Please include the theorem or definition name when reporting a concern.
