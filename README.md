# Square-difference-free sets: exponent 0.7580758318

The project proves a **general asymptotic interval-moment criterion**, and
specializes it to the exponent **0.7580758318008816**
(`473797394875551/625000000000000`). For every positive epsilon, it concludes
that all sufficiently large \(N\) have a square-difference-free subset of
\([1,N]\) of size at least \(N^{0.7580758318008816-\varepsilon}\). This is
Theorem 1.1 of the
[full paper](papers/square-difference-free-sets-of-exponent-0.7580758318.pdf).

**All nine construction components are proved, with no remaining certificate
hypotheses.** Lean constructs and checks all six prime chains, the entire
binary component, and both odd components, including every numerical moment.

Subject classifications: **math.NT** (Number Theory), **math.CO** (Combinatorics);
MSC2020 **11B75** (Other combinatorial number theory) and **05D05** (Extremal set theory).

The full theorem is `Sarkozy.record_exponent` in
[FullTarget.lean](Sarkozy/FullTarget.lean). Its independently stated submission
form, `SarkozySubmission.improved_bound` in [Solution.lean](Solution.lean),
spells out the exact rational exponent and the square-difference-free conclusion.
The numerical certificates are checked by the kernel; their generators are
not trusted assumptions.

See the [verification record](verification/README.md) for check coverage, the
[self-contained mathematical proof](PROOF.md) for the argument, and the
[semantic audit](SEMANTIC-AUDIT.md) for an adversarial review of the exact theorem.

The September 2026 version of this package proved the earlier exponent
`0.75806746`; it is registered as version 1 of Palomar entry
PALOMAR-2026-09-19-000006 and preserved in git history (commit
`e5d693729e23762b063a55015ad79ccaf28a3217`). The October 2026 port keeps every
general theorem and changes only the finite data, the odd interface (which now
allows different digit depths at the two primes of an odd component), and the
precision of the numerical certificates. The [cleanup report](CLEANUP.md)
describes the earlier size reduction of the September version.

## Papers

| Paper | PDF | Self-contained LaTeX |
|---|---|---|
| Full result: exponent **0.7580758318008816** | [Read](papers/square-difference-free-sets-of-exponent-0.7580758318.pdf) | [Source](papers/square-difference-free-sets-of-exponent-0.7580758318.tex) |
| Simpler companion: exponent **0.758001** | [Read](papers/a-simpler-construction-of-square-difference-free-sets-beyond-exponent-0.758.pdf) | [Source](papers/a-simpler-construction-of-square-difference-free-sets-beyond-exponent-0.758.tex) |

Both sources include their bibliography and exact computational certificates.
[Paper instructions](papers/README.md) explain compilation and the attached
certificate programs. The Lean project formalizes the full result.

The author is **Eric Naslund**, [naslund.math@gmail.com](mailto:naslund.math@gmail.com).
Both papers disclose the AI models' role under his prompting and supervision
(GPT-6-Astra wrote both; Claude Opus 5.5 revised the full paper in October 2026),
with his supplied note on reading the papers through questions to an AI model
before the abstract. Citation metadata is in [CITATION.cff](CITATION.cff).

This public result repository is separate from the
[working research repository](https://github.com/enaslund/sarkozy-lower-bound).
For each version, the Lean sources and dependency pins were copied unchanged
from a verified snapshot of that repository. [PUBLICATION.md](PUBLICATION.md)
records each import and the later paper front-matter, licensing, and
submission-preparation changes.

## Build

Run from the repository root (the `master/` worktree in the local bare-repository layout).
With Lean/Elan already installed:

```bash
./scripts/build-sequential.sh
```

The [build script](scripts/build-sequential.sh) completes seven large certificate
targets one at a time, then runs the full `lake build` and axiom audit. This
reduces overlap between expensive checks and uses the caller's Lean environment.

`source env.sh` selects this checkout's `.elan` installation. A fresh copy
does not include that installation: follow the steps below, or use an
existing Lean/Elan environment with the pinned toolchain available.

The build prints two expected warnings for the deliberate statement
placeholders in `Challenge.lean`. The proved library and `Solution.lean`
have no `sorry`, custom axioms, or `native_decide`. Exact rational checks use
`decide +kernel`, which evaluates in Lean’s trusted kernel. The inspected
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The project pins Lean **v4.35.0-rc2** and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; `lake-manifest.json` records
all dependency revisions. Every Lean file uses the module system: it begins
with `module`, imports with `public import`, and exposes its declarations
through `@[expose] public section` (with `backward.privateInPublic`, so the
generated private certificate chunks stay usable). The generators emit this
header through [scripts/lean_module.py](scripts/lean_module.py).
Elan **4.2.4** manages the local toolchain.
`env.sh` changes only the current shell. Toolchains and downloaded caches
are ignored by Git. Comparator uses a separate build toolchain.

## What is proved

The general theorem starts with a nonempty finite family of finite digit sets
in pairwise coprime square bases \(b_i>1\), an exponent \(\alpha\ge0\),
and intervals inside \([0,1]\), with common bounds
\(0<\sigma\le w_x\le\rho<1\). Modular square differences must order the
intervals. If
\[
\sum_{x\in C_i}w_{i,x}^{f_i}\ge b_i^\alpha,\qquad
f_i\ge0,\qquad \sum_i f_i>\alpha,
\]
then the exponent \(\alpha\) is attainable in the all-large-\(N\) sense.

The proof builds nested word intervals, stops words at a common width,
selects one length in each component by a finite moment argument, and
rounds interval positions into ranks. CRT and reverse-rank representatives
give one finite block with sufficient growth. Repeating that block and
interpolating between geometric scales proves the asymptotic conclusion.
This route avoids entropy, Stirling's formula, and frequency rounding.

For the key counting step, stop a word when the product of its widths first
falls below \(\delta=\rho^K\). All words stop by depth \(K\), and their
widths lie between \(\sigma\delta\) and \(\delta\). If
\(Z=\sum_x w_x^f\ge q=b^\alpha\), the active and newly stopped moments obey
\(A_{j+1}+T_j=Z A_j\), with \(A_0=1\) and \(A_K=0\).
A finite sum argument selects one length \(k\le K\) with at least
\(b^{k\alpha}/((K+1)\delta^f)\) words. Across components, the strict gap
\(\sum_i f_i-\alpha>0\) absorbs the polynomial counting loss and the
rounded rank height, which grows at most as a constant times \(1/\delta\).

The target uses bases
\(3^2,7^2,11^2,31^2,59^2,103^2,215^6,(19^3\cdot 23^2)^2,4^{10^{20}}\).
All nine contributions are exact 25-decimal rationals. Lean proves the sum of
**all nine** contributions minus the target exponent is exactly
\(15468032462/10^{25}>0\). The huge binary power is handled symbolically.

| Files | Proved content |
|---|---|
| [Ranked.lean](Sarkozy/Ranked.lean), [CRT.lean](Sarkozy/CRT.lean) | Finite rank construction, CRT, cardinality, and interval bounds. |
| [Words.lean](Sarkozy/Words.lean) | Square-base word lifting and geometric families. |
| [Intervals.lean](Sarkozy/Intervals.lean) | Affine interval words, exact width moments, and interval-to-rank rounding. |
| [Stopping.lean](Sarkozy/Stopping.lean) | Finite stopping-word selection and its counting estimate. |
| [Growth.lean](Sarkozy/Growth.lean), [Moment.lean](Sarkozy/Moment.lean) | Contribution budget and the general interval-moment exponent theorem. |
| [Asymptotic.lean](Sarkozy/Asymptotic.lean), [Certificate.lean](Sarkozy/Certificate.lean) | Geometric interpolation and reusable finite certificate criteria. |
| [Parameters.lean](Sarkozy/Parameters.lean), [Target.lean](Sarkozy/Target.lean) | Exact target parameters and the conditional target exponent. |
| [FiniteAlphabets.lean](Sarkozy/FiniteAlphabets.lean), [ReducedTarget.lean](Sarkozy/ReducedTarget.lean) | Indexed alphabet realization, automatic uniform width bounds, and the target from only three expanded certificates. |
| [PrimeChains.lean](Sarkozy/PrimeChains.lean), [ChainMoments.lean](Sarkozy/ChainMoments.lean) | All six explicit prime chains, geometry, and rigorous numerical moments; no remaining hypotheses. |
| [OddLift.lean](Sarkozy/OddLift.lean), [OddTarget.lean](Sarkozy/OddTarget.lean) | Prime-coordinate first differences, arbitrary-depth free-digit lifts, CRT multiplicities, and exact moments. |
| [Binary.lean](Sarkozy/Binary.lean), [BinaryGrowth.lean](Sarkozy/BinaryGrowth.lean), [BinaryPolicy.lean](Sarkozy/BinaryPolicy.lean) | Modulo-eight geometry, transformed branches, recursive alphabets, exact moments, growth, and final shrinking. |
| [BinaryData.lean](Sarkozy/BinaryData.lean), [BinaryRealData.lean](Sarkozy/BinaryRealData.lean), [RecordBinaryTarget.lean](Sarkozy/RecordBinaryTarget.lean) | Exact full-record policy, rational-to-real proof, seed/vector checks, and binary target from row/depth numerical inequalities. |
| [BinaryRows.lean](Sarkozy/BinaryRows.lean), [BinaryDepth.lean](Sarkozy/BinaryDepth.lean) | All 25 binary growth inequalities, through endpoint power certificates for the 73 distinct scales, and the fixed-depth inequality at depth `10^20`. |
| [TwoOddTarget.lean](Sarkozy/TwoOddTarget.lean) | Full target from only two expanded odd certificates; the binary component is unconditional. |
| [OddCertificate.lean](Sarkozy/OddCertificate.lean), [OddFiniteCertificate.lean](Sarkozy/OddFiniteCertificate.lean), [ActualOddTarget.lean](Sarkozy/ActualOddTarget.lean) | Finite relation reflection and transport of fixed integer witness data. |
| [OddOrder.lean](Sarkozy/OddOrder.lean), [OddOrderCertificate.lean](Sarkozy/OddOrderCertificate.lean), [OddOrder215.lean](Sarkozy/OddOrder215.lean) | Compressed predecessor-mask soundness, with a separate depth at each prime, and every edge of the actual 215 witness. |
| [PowerChecker.lean](Sarkozy/PowerChecker.lean), [PowerPolynomial.lean](Sarkozy/PowerPolynomial.lean), [FastPowerCertificate.lean](Sarkozy/FastPowerCertificate.lean) | Exact Taylor/logarithm enclosures and the shared natural-number checker for both odd witnesses. |
| [Odd215MomentData.lean](Sarkozy/Odd215MomentData.lean), [Odd215Threshold.lean](Sarkozy/Odd215Threshold.lean) | All 1,861 actual 215 power certificates, using the shared checker, and the scalar threshold. |
| [OddMoments.lean](Sarkozy/OddMoments.lean), [Odd215Moment.lean](Sarkozy/Odd215Moment.lean), [Odd215Certificate.lean](Sarkozy/Odd215Certificate.lean) | Histogram transport, the actual 215 moment, and its complete expanded alphabet. |
| [OddData437.lean](Sarkozy/OddData437.lean), [OddOrder437.lean](Sarkozy/OddOrder437.lean) | All 3,645 actual `(19,23)` rows, with three digits at 19 and two at 23: coordinates, distinctness, interval geometry, and every required first-difference edge. |
| [Odd437MomentData.lean](Sarkozy/Odd437MomentData.lean), [Odd437Moment.lean](Sarkozy/Odd437Moment.lean), [Odd437Threshold.lean](Sarkozy/Odd437Threshold.lean) | All 3,337 distinct-width power bounds and the full actual `(19,23)` moment. |
| [Odd437Certificate.lean](Sarkozy/Odd437Certificate.lean), [FullTarget.lean](Sarkozy/FullTarget.lean) | Complete expanded `(19,23)` alphabet and the unconditional full exponent. |
| [OneOddTarget.lean](Sarkozy/OneOddTarget.lean) | Full exponent from one expanded `(19,23)` certificate, or only two checks on its fixed low rows. |
| [RecordTarget.lean](Sarkozy/RecordTarget.lean) | Earlier general interface to two arbitrary odd low-support certificates. |
| [QuantitativeExamples.lean](Sarkozy/QuantitativeExamples.lean) | Unconditional `6^k` elements in `[1,18^k]` and exponent `3/5`; all hypotheses proved. |
| [Examples.lean](Sarkozy/Examples.lean) | The original two- and six-element finite examples. |

## Complete finite certificates

The Lean module names keep `215` and `437` for the odd components at the
primes `(5,43)` and `(19,23)`. The `(5,43)` witness has 4,913 points with three
restricted digits at each prime. The `(19,23)` witness has 3,645 points with
three restricted digits at 19 and two at 23, so its square base is
\((19^3\cdot23^2)^2\) and each low point has \(19^3\cdot23^2=3628411\)
free-digit copies. Kernel-checked predecessor masks prove every required edge
ordering; the checker takes a separate depth for each prime. Exact
width-histogram identities connect the endpoint-sorted geometric rows to their
numerical certificates.

The contribution surplus is only \(1.5\cdot10^{-15}\), and the odd moment and
binary growth margins are about \(10^{-18}\), so all numerical certificates
are much more precise than in the September version:

- the 1,861 and 3,337 distinct odd widths, and the 73 distinct binary scales,
  use exact 4096th-power comparisons at denominator \(10^{30}\) and an
  eighth-order logarithm enclosure, with lower bounds over \(10^{24}\)
  (\(10^{30}\) for the binary scales);
- the odd thresholds and the binary depth use 80-step square-root ladders at
  denominator \(10^{50}\);
- the six chain logarithms use 100-step ladders at denominator \(10^{60}\),
  since their margins are about \(2.4\cdot10^{-26}\).

The certified odd log margins are \(6.919\cdot10^{-18}\) and
\(5.927\cdot10^{-18}\), the smallest binary row surplus is
\(3.274\cdot10^{-19}\), and the fixed-depth margin is at least 45. Every
comparison is exact: high-precision Decimal arithmetic in the generators only
proposes the integer certificates.

[Odd215Certificate.lean](Sarkozy/Odd215Certificate.lean) and
[Odd437Certificate.lean](Sarkozy/Odd437Certificate.lean) construct the complete
expanded odd alphabets without assumptions. All six prime chains and the
entire binary component are also unconditional; the latter includes all 25
growth rows and the fixed-depth inequality.

No finite-certificate, recursive-construction, free-digit-lifting, counting,
or asymptotic hypothesis remains in `record_exponent`. The older unconditional
`3/5` example remains an illustration.

The generators are in [scripts/](scripts/): `generate-odd437-data.py`,
`generate-odd437-order.py`, `generate-odd437-order-chunks.py`,
`generate-odd215-moments.py`, `generate-odd437-moments.py`,
`generate-odd-thresholds.py`, `generate-binary-data.py` (with the binary
certificate path as argument), `generate-binary-rows.py`,
`generate-binary-depth.py` and `generate-chain-log-bounds.py`; the (5,43)
witness, unchanged since September, comes from `generate-odd-data.py`,
`generate-odd-order.py` and `generate-odd-order-chunks.py`. Each reads the
pinned witness in the working repository's `research-notes/` (see
[scripts/README.md](scripts/README.md)) and checks its own output exactly
before writing. All of them reproduce the included Lean files byte for byte.

## Research context and provenance

This development is intended for researchers studying constructive lower
bounds and finite certificate methods in additive combinatorics.
[Krachun's 2026 paper](https://arxiv.org/abs/2608.01325v1) proves exponent
`0.7527964558…` using ranked blocks and CRT. Its Lemmas 4 and 5 supply the
ranked realization and gluing ideas used here; our ranks increase, with
reverse-rank integer representatives. We do not formalize the paper's
full numerical theorem.

The general criterion permits unequal interval widths and isolates a finite
moment condition that future searches can try to satisfy. Its formal proof
uses stopping words in place of the entropy argument in the unpublished
September 2026 research notes. The proposed submission includes this reusable implication and its fully
verified numerical application. We do not assert independent novelty of the
general criterion or bibliographic priority for the package.

The working notes named `METHODS.md` and `CAPACITY-IMPROVEMENT.md` are not
distributed here. [PROOF.md](PROOF.md) restates the complete argument that is
formalized, so those notes and the external computations are unnecessary
to read or check this package. [formalization.yaml](formalization.yaml)
records source relationships, human direction, agent assistance, and the
absence of asserted source-author endorsement or human peer review.

## Submission files and verification

This revision is prepared as version 2 of
[PALOMAR-2026-09-19-000006](https://palomar-registry.org/entry?id=PALOMAR-2026-09-19-000006&version=1).
**The official full preflight passed on 2026-10-07** for commit
`389566cfec3a14ace44fe554558d824310351214` in [run 37552134159](https://github.com/enaslund/sarkozy-lower-bound-0.758/actions/runs/37552134159)
(PalomarSubmission `d4e41c1d5b0d`, profile `palomar-standard-v1`, `existing_id`
PALOMAR-2026-09-19-000006): `status: pass`, `stage: complete`, no errors or
warnings. Both selected theorems passed the protected canonical-Challenge audit
and `lake comparator` with con-ron (29,813 declarations), NanoDa and Lean's
kernel, and all 117 Lean files passed the module-system and line-count check.
The [mechanical report](verification/palomar-preflight-20261007.json) is preserved;
later commits change only documentation.
Version 1 passed the service's
[mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/35424167849)
on 2026-09-19 for commit `4de015dae4f256ea9af929727f70afa8ee118c74`, and was
registered from the metadata revision `e5d693729e23762b063a55015ad79ccaf28a3217`;
its [mechanical report](verification/palomar-submission-20260919.json) and the
earlier [preflight report](verification/palomar-preflight-20260918.json) are
preserved. Each verdict applies to its exact source commit. See
[SUBMISSION.md](SUBMISSION.md) for the version-2 fields and
[PUBLICATION.md](PUBLICATION.md) for the revision history.

[Challenge.lean](Challenge.lean) selects two related results using Mathlib alone:
the general interval-moment criterion and the unconditional numerical
application, `improved_bound`. [Solution.lean](Solution.lean) proves both.
[comparator.json](comparator.json) compares these two declarations. The finite
CRT theorem, the `3/5` example, and the older nine-certificate application remain
proved library results. The exported numerical proof includes all nine component certificates.
Additional interfaces to the original row orders are included in the ordinary
Lean build and axiom audit.
[formalization.yaml](formalization.yaml) records scope, provenance, and AI
assistance; [Check.lean](Check.lean) prints axiom dependencies.

The current source (Lean v4.35.0-rc2, module system) passed a clean rebuild,
the 76 standard-axiom inspections, `leanchecker` kernel replays of every
project module and of the full dependency closure of `Solution` from an empty
environment, and the bundled `lake comparator` with Lean's kernel, NanoDa and
con-ron; see the [verification record](verification/README.md). The hosted
checks, which compare against Palomar's protected canonical Challenge, and
their exact source commits are in
[Palomar mechanical preflight runs](https://github.com/enaslund/sarkozy-lower-bound-0.758/actions/workflows/palomar-preflight.yml).
The local NanoDa replay of 32,704 declarations and the incomplete local
Comparator attempts recorded there belong to the September source for
exponent `0.75806746`.

The mathematical formalization is complete. Palomar registration requires the
service's mechanical verification and editorial review. Our optional
[full mechanical preflight](.github/workflows/palomar-preflight.yml) runs the
official verifier, including the protected Challenge audit and both kernels,
at a pinned pipeline revision. To run the comparator check locally:

```bash
./scripts/verify-comparator.sh
```

The script runs `lake comparator`, which ships with the pinned Lean toolchain,
on `comparator.json` with the external kernels NanoDa and con-ron, the same
kernels Palomar's verifier registers. It builds and exports the project in a
bubblewrap sandbox, so it needs `bwrap` with user namespaces available; it
needs neither Go nor Rust. The [verification record](verification/README.md)
contains the exact commands, logs and source hashes.

The [ordinary CI workflow](.github/workflows/ci.yml) provides the Lean build,
axiom inspection, and local Comparator setup. Both it and the official
preflight are manual (`workflow_dispatch`). The official preflight uses
`mode: full`; its mechanical report records the precise verdict and source SHA.
It is predictive preparation, not a Palomar submission.
[SUBMISSION.md](SUBMISSION.md) gives the workflow commands and submission fields.

**Palomar status.** Version 1 of this entry, for exponent `0.75806746`, is
registered as
[PALOMAR-2026-09-19-000006](https://palomar-registry.org/entry?id=PALOMAR-2026-09-19-000006&version=1),
submitted on 2026-09-19 from commit `e5d693729e23762b063a55015ad79ccaf28a3217`.
The present source, for `0.7580758318008816`, is prepared as version 2 of the
same entry from this repository; it is registered only if the service accepts
that update. The [Apache-2.0 license](LICENSE)
covers this repository's original work, including the Lean formalization,
documentation, both papers (LaTeX and PDF), certificate programs, and generated
data. It permits use, modification, and redistribution, including commercial
use, subject to its notice and other terms. [NOTICE](NOTICE) records attribution;
cited external works and dependencies retain their own licences.
Local verification does not establish Palomar's research-interest judgment.

## Recreate the Lean installation

In a fresh checkout, direct the
[official Elan installer](https://lean-lang.org/install/manual/) to this folder:

```bash
source env.sh
curl --proto '=https' --tlsv1.2 -fsSL \
  https://elan.lean-lang.org/elan-init.sh -o /tmp/sarkozy-elan-init.sh
sh /tmp/sarkozy-elan-init.sh -y --no-modify-path --default-toolchain none
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
./scripts/build-sequential.sh
```

The initial downloads need network access. Cached builds work locally.
For VS Code, open this folder from a shell with `env.sh` sourced and use
the official Lean 4 extension.
