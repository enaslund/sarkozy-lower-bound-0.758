# Potential Palomar submission

The proposed submission is the **general interval-moment criterion for
square-difference-free integer sets**. It turns finite ordered interval
alphabets and a strict moment surplus into an asymptotic lower bound for
every sufficiently large ambient interval. The stopping-word proof is the
main mathematical development; the fixed exponent is an application.

The exponent `0.75806746` is proved without certificate hypotheses. All nine
components are formalized: six prime chains, both odd witnesses, and the
complete binary construction with every numerical check. The library theorem
`Sarkozy.record_exponent` derives the full bound from these concrete certificates.

The numerical Comparator statement, `improved_bound`, independently spells
out the unconditional all-large-N conclusion and exact rational exponent.
Its exported proof includes the ordering and moment of the actual 437 witness.
The original-row interfaces are also checked by the full build and axiom audit.
See [PROOF.md](PROOF.md), [README.md](README.md), and the
[Palomar assessment](PALOMAR-READINESS.md).

## Public repository

The public repository is
[enaslund/sarkozy-lower-bound-0.758](https://github.com/enaslund/sarkozy-lower-bound-0.758),
with default branch `master` and the Lean project at its root. Both papers
are under [papers/](papers/README.md). Select an exact pushed revision for any
later submission, using `git rev-parse HEAD` from the checkout.

[PUBLICATION.md](PUBLICATION.md) records the source import. The original
verification receipts are preserved, and the 152 frozen Lean source and
configuration files are unchanged. Publication documentation and the manual
CI trigger are listed separately in `verification/public-export.json`.
Build caches, toolchains and the research archive are not part of this repository.

The earlier ignored `dist/` packages remain in the working research checkout;
they are not required to build or inspect this public repository. After proof
changes, rerun verification before selecting a revision for submission.

| Submission field | Value |
|---|---|
| Project directory | `.` |
| Comparator configuration | `comparator.json` |
| Challenge / Solution modules | `Challenge` / `Solution` |
| Metadata | `formalization.yaml` |
| Repository and revision | `enaslund/sarkozy-lower-bound-0.758`; the full pushed SHA from `git rev-parse HEAD`. |

The selected declarations, all in namespace `SarkozySubmission`, are:

- `interval_moment_bound`: the general asymptotic criterion.
- `improved_bound`: the unconditional full exponent `37903373/50000000`.

`Solution.lean` contains exactly these two declarations, with their original
statements unchanged. Four redundant submission wrappers were removed; their
underlying finite CRT, conditional-bound and example theorems remain in the
library. The [semantic audit](SEMANTIC-AUDIT.md) checks that the numerical
statement means the intended bound for every sufficiently large `N`.

[verification/README.md](verification/README.md) records a fresh complete
Lean build, 76 standard-axiom inspections and direct pinned NanoDa replay of
the cleaned source with an 8 MiB stack. Its receipts bind the results to the
current source hashes. The earlier 32,700-declaration NanoDa pass and three
interrupted Comparator attempts belong to the preserved version before
cleanup. No successful Comparator run or hosted verification is established
for the cleaned version. The repository's `comparator.json` still enables
NanoDa.

The mathematical formalization is complete. A successful configured Comparator
run and hosted verification remain operational requirements before claiming
submission readiness. The current evidence is preparation evidence, not a
successful combined service run, Palomar verification, or registration.

## Handoff and submission

1. Review the exact statements, full numerical claim, authorship, and
   provenance in the prepared snapshot, and complete the configured Comparator
   check.
2. Select a pushed revision of this public repository and record its full
   40-character commit SHA. Palomar reviews an exact commit, not a branch or
   tag. The verification workflow is currently manual. Complete the hosted
   verification on that revision
   before claiming submission readiness. See the
   [ordinary submission requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#2-prepare-an-ordinary-submission).
3. Start at [the Palomar submission portal](https://submit.palomar-registry.org/)
   with that repository, revision, and `comparator.json`. Review the preview
   and reports before making any later registration choice.

The maintainer must honestly identify the human authors and responsible
maintainers, and state whether they are responsible for the substantive
formalization or have approval from someone who is. Source-author contact or
endorsement is a separate fact; report only what occurred. Account access
does not establish authorship, and this guide records no human endorsement
or authorization to submit. See the
[authorization policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#4-confirm-that-you-are-authorised-to-submit).

Mechanical success does not establish novelty or research interest. The
submission should explain the numerical improvement and its relevance
to researchers studying polynomial-difference-free sets. Publishing this repository does not constitute a Palomar submission or
registration. The
[official policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
governs the eventual submission.
