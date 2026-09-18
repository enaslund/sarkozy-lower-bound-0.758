# Palomar readiness assessment

Prepared on **2026-09-18** against
[PalomarPolicy `792c7c0b9e798bd02719e795ef11fa2b5929e067`](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/CONTRIBUTING.md)
and [PalomarSubmission `3561d237dcc4b28482558ad28a64d767d7cc8615`](https://github.com/PalomarRegistry/PalomarSubmission/tree/3561d237dcc4b28482558ad28a64d767d7cc8615).
This is the author's preparation record. No Palomar editorial review or
registration is claimed.

**The official full mechanical preflight passed on 2026-09-18** for candidate
commit `e26058b55ab928e321d25318185acc69fbf62ab9`.
[Run 35392867341](https://github.com/enaslund/sarkozy-lower-bound-0.758/actions/runs/35392867341)
completed in about 58 minutes. Its
[unmodified mechanical report](verification/palomar-preflight-20260918.json)
records `status: pass`, `phase: verification`, and `stage: complete`, with no
reported verification errors or policy warnings. Both selected declarations
passed Comparator, the protected Challenge audit, Lean's kernel, and NanoDa.
Later changes that preserve this report only document that checked candidate;
they are not included in its recorded source commit.

## Submission scope and structure

One Comparator configuration selects two related results:

- `SarkozySubmission.interval_moment_bound`, the general asymptotic
  interval-moment criterion proved with finite stopping words;
- `SarkozySubmission.improved_bound`, the unconditional exponent
  `37903373/50000000 = 0.75806746` for every sufficiently large ambient interval.

All nine construction components are formalized, including every ordering and
numerical moment of both odd witnesses. The numerical theorem has no remaining
certificate hypotheses. [SEMANTIC-AUDIT.md](SEMANTIC-AUDIT.md) records the
statement audit; [PROOF.md](PROOF.md) gives the formalized argument.

All conventional submission files are at repository root. `Challenge.lean`
imports only Mathlib and has 59 lines and 2,676 bytes, well below the policy
limits. Its two deliberate statement placeholders are permitted by policy;
the corresponding Solution declarations are proved. The repository has no
Git LFS pointers, submodules, or submitted compiled Lean/native artifacts.

Lean 4.32.0 exceeds the current 4.28.0 minimum and exactly matches the
[canonical Mathlib toolchain at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/lean-toolchain).
The manifest's eight transitive package revisions agree with Mathlib's
manifest, and all nine Git dependencies are public GitHub repositories pinned
to full lowercase commit SHAs.

`formalization.yaml` uses v0.4 and passes the pinned official metadata validator.
Its provenance is source-based and this repository contains the substantive
development. Sources include Krachun's ranked-block and CRT construction, the
working notes, and both accompanying manuscripts with their exact scope.
Human authorship, AI assistance, and the absence of human peer review are
disclosed. [LICENSE](LICENSE) declares Apache-2.0 for this repository's original
work, including the papers and certificate programs; [NOTICE](NOTICE) gives
the scope and attribution. The hosted preflight passed the root licence checks
and detected the declared SPDX identifier `Apache-2.0`.

## Verification evidence and current hosted checks

The preserved local evidence establishes a complete Lean build, 76 inspections
using only `propext`, `Classical.choice`, and `Quot.sound`, and direct NanoDa
replay of **32,704 declarations** with no errors. All 152 frozen Lean source
and build/configuration hashes still match the preserved successful source.
See [verification/README.md](verification/README.md).

The earlier 32,700-declaration replay and three interrupted Comparator attempts
belong to the preserved version before cleanup. Neither those attempts nor
the successful direct replay establishes the protected Challenge comparison.

The [official full mechanical preflight workflow](.github/workflows/palomar-preflight.yml)
calls Palomar's own pinned verifier with `mode: full`. It checks the licence,
metadata, canonical Challenge dependencies and statement environment,
Comparator, Lean's kernel, and independent NanoDa replay. Its
[GitHub Actions runs](https://github.com/enaslund/sarkozy-lower-bound-0.758/actions/workflows/palomar-preflight.yml)
and attached `mechanical-report.json` give the authoritative verdict for each
exact checked commit. A launched or green preparation-only job is not a proof
verification result. Consult the report's status, phase, source SHA, and
verification evidence before claiming a mechanical pass.

The standard profile has a 19,800-second execution budget within a 350-minute
job, at least 14 GiB host memory and 20 GiB free workspace. It starts with fresh
submitted Lake build state; the repository's sequential prebuild script is
not run by this official verifier. Historical local timings therefore do not
guarantee a successful hosted cold build.

Repository preflight and local Comparator are recommended preparation, not
additional policy prerequisites. Palomar itself must produce a passing
mechanical report before editorial review. The optional preflight neither
starts that review nor registers the result.

## Remaining service steps

Use the verified candidate `e26058b55ab928e321d25318185acc69fbf62ab9`, or a
later deliberately selected pushed 40-character commit, and explicitly select
`comparator.json`. **Leave the project-path field blank** for the repository
root; do not enter `.`. The default metadata path is `formalization.yaml`.
[SUBMISSION.md](SUBMISSION.md) gives the commands and submission fields.

The automated editorial review must find no blocking issue in statement
alignment, definitions, provenance, literature, and research interest.
The interval-moment criterion and its numerical application are directed at
researchers in constructive additive combinatorics. Attribution to Krachun
remains explicit; independent novelty of the general criterion and bibliographic
priority are not asserted. Mechanical verification does not settle these
editorial questions.

Registration is a separate decision after the review is delivered, and creates
permanent source-preservation and version history under the
[Palomar protocol](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/docs/specification.md).
