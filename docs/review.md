# Publication Content Review

Review date: 2026-10-24.

## Publication scope

This directory is an isolated publication candidate. It contains the complete 340-module proof collection, an English idea note, a result map, literature context, and reproducible verification. The original internal research packages are preserved separately.

The 340 Lean files are byte-for-byte identical to the previously verified source baseline. Their comments and declaration names were already in English. Public prose has been rewritten in English and organized around mathematical results rather than internal stages.

Internal Chinese reports, their generators, duplicated historical source snapshots, local review bundles, and process records are not included. This is a curated publication, not a language conversion of every historical project file.

## Mathematical wording reviewed

- The base includes full first-order Separation and Collection as well as Power Set.
- Internal behavior is not equated with arbitrary external bisimilarity.
- The exact no-choice lift retains its external countability assumption.
- The arbitrary-input lift gives an elementary embedding, not a surjection.
- Model-existence results remain conditional and semantic.
- AC2 means exactly two distinct members and arbitrary internal families.
- No orientation of an input pair family is assumed.
- FC2 and QC2 are classified as equivalent to AC2 under BAFA, not as new-strength axioms.
- The AFA vacuity result is not a proof of AC2.
- No strict separation of AC2 from full AC is asserted.
- The original sentence is distinguished from its behavior translation.
- Metatheoretic choice is distinguished from object-level choice.
- Formal correctness is distinguished from novelty and independent expert review.

## Reproducibility and automated checks

The publication verifier compiles from a fresh temporary directory and audits every named theorem. Its command log uses the executable name instead of a personal installation path. The Lean output itself is retained. Consult the generated verification manifest for the actual result of the current run.

Run `python3 audit_publication.py` after a successful verification to check source identity, verifier and toolchain hashes, filename and text language screening, local Markdown links, machine-specific paths, and common credential patterns. The audit record reports the checks actually performed. Pattern checks are not a guarantee of detecting every possible private datum or determining the language of every sentence.

Human-readable prose was reviewed for English wording. Standard Lean mathematical symbols are retained. The bibliography retains scholarly names and titles.

## Remaining release metadata

The publication destination is the public repository `ruochenouyang-wq/non-well-founded-sets`. This account was confirmed through the signed-in GitHub interface. No separate personal author identity or reuse license has been selected. The content review preceded publication.
