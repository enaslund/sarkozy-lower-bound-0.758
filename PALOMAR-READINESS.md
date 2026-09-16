# Palomar readiness assessment

Checked against the official policy on **2026-09-11**. This is a local
assessment; Palomar has not reviewed or accepted the project. The exact
verified source and replay coverage are recorded in
[verification/snapshot.json](verification/snapshot.json).

The proposed submission is a **general interval-moment criterion and an
unconditional application to exponent 0.75806746**. All nine components are
fully formalized, including the ordering and numerical moments of both odd
witnesses. `Sarkozy.record_exponent` has no finite-certificate hypotheses.

Palomar prohibits custom axioms and `native_decide`, allowing only `propext`,
`Classical.choice` and `Quot.sound`. The audited proofs use only these standard
axioms. Integer data generators are not trusted by the proofs; the finite
certificates use kernel reduction. The complete numerical theorem no longer
needs Palomar's allowance for explicit mathematical hypotheses.
[Official submission guidance](https://palomar-registry.org/how-to-submit).

The package selects two related statements: `interval_moment_bound` and
`improved_bound`; these are now the only declarations in `Solution.lean`.
Their statements are unchanged by the cleanup. The latter independently
states the exact rational exponent and full all-large-N conclusion. Its
exported proof includes all nine component certificates. The
[semantic audit](SEMANTIC-AUDIT.md) found no weakened statement, hidden
certificate hypothesis or mismatch with the intended lower bound. Original-row moment interfaces and supporting theorems are also
included in the full library build and axiom audit. The Challenge imports only
Mathlib and stays well below the policy limits. Pinned dependencies, an
Apache-2.0 license, and v0.4 provenance metadata are included. The project
uses Lean 4.32.0, above the service minimum inspected on that date.
[Submission requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
[minimum toolchain](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json).

The verifier launcher uses the service's Comparator commit inspected on
2026-09-11, `575674928e239f5bc452aab72d1dd7b0f1326494`, using its
separate Lean 4.34.0-rc1 build toolchain. The proof project and its matched
exporter remain on Lean 4.32.0. The launcher now uses Landrun directly;
the old compatibility wrapper is not needed. The cleaned source passed a
fresh complete Lean build, 76 standard-axiom inspections and a complete
direct NanoDa replay with an 8 MiB stack. The shared integer power checker,
compact certificate encodings and proof-only data annotations retain kernel
checking of every numerical comparison.

The earlier 32,700-declaration NanoDa pass is preserved with the source
snapshot before cleanup. The three Comparator attempts that received
unexplained SIGTERM also apply to that earlier version. None establishes
current Comparator success. A complete Comparator replay and
statement-comparison pass for the cleaned source remain outstanding.
The repository configuration still enables NanoDa. See the verification
record for exact sources, commands, sandbox scope and results.
[Service workflow](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/.github/workflows/submission.yml).

These local checks do not settle Palomar's research-interest or
alignment review. The policy evaluates each distinct selected result group,
allowing related corollaries to be grouped. The general criterion and its
numerical application form the clearest proposed group. Attribution to
Krachun's ranked-block and CRT arguments must remain explicit; this package
does not claim formalization of his full numerical theorem or independent
novelty of the general criterion.
[Research-interest review](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/prompts/04-literature-notability.md).

The mathematical formalization is complete for the stated exponent. Further
work could improve checking speed or simplify proof organization, but these
are maintenance improvements rather than missing proof obligations. A successful
configured Comparator run and hosted verification remain operational requirements
before claiming submission readiness. Mathematical completion does not establish
that this exponent is optimal or settle bibliographic priority.

For any eventual submission, select an exact pushed 40-character commit of
[this public repository](https://github.com/enaslund/sarkozy-lower-bound-0.758). Local Comparator does not reproduce
the service's protected canonical-Challenge audit or its editorial review.
This repository is public. Hosted CI, official review and Palomar
registration have not been performed. The ordinary Lean build and direct NanoDa pass are not a successful
combined verification run, acceptance or endorsement.
[Submission specification](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/docs/specification.md).
