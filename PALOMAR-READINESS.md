# Palomar readiness assessment

Version-2 assessment prepared on **2026-10-06** against
[PalomarPolicy `96b034cc31a72a63d4f4041911dce337a85c9a04`](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md)
and [PalomarSubmission `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`](https://github.com/PalomarRegistry/PalomarSubmission/tree/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44).
This is the author's preparation record.

**Status.** Version 1 of this entry, for exponent `0.75806746`, is registered as
[PALOMAR-2026-09-19-000006](https://palomar-registry.org/entry?id=PALOMAR-2026-09-19-000006&version=1)
from commit `e5d693729e23762b063a55015ad79ccaf28a3217`. The present revision
proves `0.7580758318008816` and is prepared as version 2 of the same entry.
Its official hosted preflight runs from the workflow described below; the verdict is added here once it completes.
The service's own mechanical run, review and registration decision for version 2
are still to come.

## What changes in version 2

The same Comparator configuration selects the same two declarations:

- `SarkozySubmission.interval_moment_bound`, the general asymptotic
  interval-moment criterion proved with finite stopping words (statement
  unchanged);
- `SarkozySubmission.improved_bound`, now with the unconditional exponent
  `473797394875551/625000000000000 = 0.7580758318008816` (version 1:
  `37903373/50000000 = 0.75806746`).

The general theory is unchanged. The construction uses new finite witnesses:
a 4,913-point (5,43) code with depths (3,3) (as before) and a new 3,645-point
(19,23) code with depths (3,2) (previously 19,683 points at depth 3); the odd
interface therefore allows a separate digit depth at each prime. The binary
recursion is evaluated at depth `10^20`, and every numerical certificate is
regenerated at higher precision. All nine components remain fully proved with
no certificate hypotheses. [SEMANTIC-AUDIT.md](SEMANTIC-AUDIT.md) records the
statement audit; [PROOF.md](PROOF.md) gives the formalized argument. The
accompanying paper is replaced by its October revision for the new exponent.

Section 9 of the policy describes later versions as corrections or dependency
updates citing the existing identifier, with the same repository, project path
and Comparator configuration path. All three are unchanged (repository
`enaslund/sarkozy-lower-bound-0.758`, repository root, `comparator.json`), and
the new source commit is not in the entry's history. This version also
strengthens the numerical statement. Whether that is accepted as version 2 or
should instead become a new entry is the service's editorial decision; the
submission states the change plainly.

## Mechanical requirements

| Requirement (policy section 2) | This revision |
|---|---|
| Toolchain no older than `toolchains.json` minimum `v4.35.0-rc2` | `leanprover/lean4:v4.35.0-rc2` |
| Toolchain equals pinned Mathlib's `lean-toolchain` | Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` pins `v4.35.0-rc2` |
| Committed manifest consistent with Mathlib | all eight transitive revisions equal Mathlib's manifest; all pinned to full SHAs |
| Every `.lean` file uses the module system | all 117 files begin with `module` |
| At most 10,000 physical lines per `.lean` file | largest is 6,032 lines (`Sarkozy/OddOrderData437.lean`) |
| Challenge at most 1,000 lines and 100 KiB | 64 lines, 2,780 bytes, imports only Mathlib |
| No LFS pointers, submodules or compiled artifacts | none |
| Metadata `formalization.yaml` v0.4 | passes `load_formalization_metadata` of the pinned PalomarSubmission |

The port to the module system makes every declaration public
(`@[expose] public section` with `backward.privateInPublic`), so the
Challenge/Solution interface and all certificate chunks stay usable. The
Challenge's two statements and their deliberate `sorry` placeholders are
unchanged apart from the new exponent literal and the module header.

## Verification evidence

The [verification record](verification/README.md) gives commands, logs and
hashes. In summary, on Lean v4.35.0-rc2:

- a clean rebuild of every project module, run as the sequential build
  script does;
- 76 axiom inspections, all using only `propext`, `Classical.choice` and
  `Quot.sound`;
- `leanchecker` replays of every project module and of the full dependency
  closure of `Solution` in an empty environment;
- `lake comparator` (the toolchain's bundled comparator, which the current
  verifier uses) with the external kernels NanoDa and con-ron, judging both
  selected theorems against the repository's Challenge.

Palomar's hosted run additionally replaces the Challenge with a protected
canonical copy and runs the comparator in its own sandbox. The
[official preflight workflow](.github/workflows/palomar-preflight.yml) calls the
pinned verifier with `mode: full` and `existing_id` set to this entry, and its
[runs](https://github.com/enaslund/sarkozy-lower-bound-0.758/actions/workflows/palomar-preflight.yml)
attach the authoritative `mechanical-report.json` for each exact commit.

The preflight selects the GitHub-hosted profile `palomar-standard-v1`: a
19,800-second execution budget within a 350-minute job, at least 14 GiB of host
memory and 20 GiB of free workspace. Palomar's own run uses its default profile,
a Namespace runner with 16 cores and 30 GiB and the same time limits, so a pass
on the smaller hosted runner is the stricter test. Both build from fresh Lake
state without the sequential build script. Locally (16 cores) the clean rebuild
took 9 minutes and the comparator 77 minutes, with peak memory near 2.5 GB.

## Metadata, licence and classifications

`formalization.yaml` describes version 2: the new exponent and witnesses, the
toolchain, a second automation method (Claude Opus 5.5 in Claude Code, which
ported the formalization and revised the manuscript), and the version history.
Human authorship, AI assistance and the absence of human peer review remain
disclosed. [LICENSE](LICENSE) declares Apache-2.0 for this repository's original
work, including the papers and certificate programs; [NOTICE](NOTICE) gives
the scope and attribution. The classifications are unchanged:

| Taxonomy | Code | Subject |
|---|---|---|
| arXiv | `math.NT` | Number Theory |
| arXiv | `math.CO` | Combinatorics |
| MSC2020 | `11B75` | Other combinatorial number theory |
| MSC2020 | `05D05` | Extremal set theory |

## Remaining service steps

Submit the pushed 40-character commit through the
[portal](https://submit.palomar-registry.org/) as an update of
**PALOMAR-2026-09-19-000006**: leave the project path blank (repository root;
`.` is rejected), select the root `comparator.json`, and keep the default
`formalization.yaml`. [SUBMISSION.md](SUBMISSION.md) lists every field.

The automated editorial review must again find no blocking issue in statement
alignment, definitions, provenance, literature and research interest.
Attribution to Krachun remains explicit; independent novelty of the general
criterion and bibliographic priority are not asserted. Mechanical verification
does not settle these editorial questions, and registering version 2 is a
separate decision after the review is delivered.
