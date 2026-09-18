# Square-difference-free sets: exponent 0.75806746

The project proves a **general asymptotic interval-moment criterion**, and
specializes it to the exponent **0.75806746**. For every positive epsilon,
it concludes that all sufficiently large \(N\) have a square-difference-free
subset of \([1,N]\) of size at least \(N^{0.75806746-\varepsilon}\).

**All nine construction components are proved, with no remaining certificate
hypotheses.** Lean constructs and checks all six prime chains, the entire
binary component, and both odd components, including every numerical moment.

The full theorem is `Sarkozy.record_exponent` in
[FullTarget.lean](Sarkozy/FullTarget.lean). Its independently stated submission
form, `SarkozySubmission.improved_bound` in [Solution.lean](Solution.lean),
spells out the exact rational exponent and the square-difference-free conclusion.
The numerical certificates are checked by the kernel; their generators are
not trusted assumptions.

See the [verification record](verification/README.md) for check coverage, the
[self-contained mathematical proof](PROOF.md) for the argument, and the
[semantic audit](SEMANTIC-AUDIT.md) for an adversarial review of the exact theorem.
The [cleanup report](CLEANUP.md) separates certificate size from proof size.

The cleanup preserves both selected theorem statements, every geometric row,
and every width, multiplicity and certified lower bound. Lean source shrank from 32,409,807 to 10,497,588 bytes
(67.6%): trailing zero bits in masks are stored as
shifts, odd width-power certificates store two root endpoints and derived initial scalings,
and both odd witnesses share one proved integer power checker. Large proof
data avoid unused executable code generation through `noncomputable`;
their values remain reducible and checked by the kernel. The submission file
now contains only its two selected results, while the underlying construction
and conditional theorems remain in the library.

## Papers

| Paper | PDF | Self-contained LaTeX |
|---|---|---|
| Full result: exponent **0.75806746** | [Read](papers/square-difference-free.pdf) | [Source](papers/square-difference-free.tex) |
| Simpler companion: exponent **0.758001** | [Read](papers/sarkozy_simple_0.758.pdf) | [Source](papers/sarkozy_simple_0.758.tex) |

Both sources include their bibliography and exact computational certificates.
[Paper instructions](papers/README.md) explain compilation and the attached
certificate programs. The Lean project formalizes the full result.

The author is **Eric Naslund**, [naslund.math@gmail.com](mailto:naslund.math@gmail.com).
Both papers disclose GPT-6-Astra's role under his prompting and supervision,
with his supplied note on reading the papers through questions to an AI model
before the abstract. Citation metadata is in [CITATION.cff](CITATION.cff).

This public result repository is separate from the
[working research repository](https://github.com/enaslund/sarkozy-lower-bound).
The Lean sources and dependency pins were copied unchanged from its verified
snapshot. [PUBLICATION.md](PUBLICATION.md) records the import and the later
paper front-matter, licensing, and submission-preparation changes.

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

The project pins Lean **4.32.0** and Mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`; `lake-manifest.json` records
all dependency revisions. Elan **4.2.4** manages the local toolchain.
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
\(3^2,7^2,11^2,31^2,59^2,103^2,215^6,437^6,4^{10^{10}}\).
The six rational chain powers are rounded down from the source parameters.
Lean proves the sum of **all nine** powers minus the target exponent is exactly
\(25671/10^{12}=0.000000025671>0\). The huge binary power is handled
symbolically.

| Files | Proved content |
|---|---|
| [Ranked.lean](Sarkozy/Ranked.lean), [CRT.lean](Sarkozy/CRT.lean) | Finite rank construction, CRT, cardinality, and interval bounds. |
| [Words.lean](Sarkozy/Words.lean) | Square-base word lifting and geometric families. |
| [Intervals.lean](Sarkozy/Intervals.lean) | Affine interval words, exact width moments, and interval-to-rank rounding. |
| [Stopping.lean](Sarkozy/Stopping.lean) | Finite stopping-word selection and its counting estimate. |
| [Growth.lean](Sarkozy/Growth.lean), [Moment.lean](Sarkozy/Moment.lean) | Contribution budget and the general interval-moment exponent theorem. |
| [Asymptotic.lean](Sarkozy/Asymptotic.lean), [Certificate.lean](Sarkozy/Certificate.lean) | Geometric interpolation and reusable finite certificate criteria. |
| [Parameters.lean](Sarkozy/Parameters.lean), [Target.lean](Sarkozy/Target.lean) | Exact target parameters and the conditional exponent `0.75806746`. |
| [FiniteAlphabets.lean](Sarkozy/FiniteAlphabets.lean), [ReducedTarget.lean](Sarkozy/ReducedTarget.lean) | Indexed alphabet realization, automatic uniform width bounds, and the target from only three expanded certificates. |
| [PrimeChains.lean](Sarkozy/PrimeChains.lean), [ChainMoments.lean](Sarkozy/ChainMoments.lean) | All six explicit prime chains, geometry, and rigorous numerical moments; no remaining hypotheses. |
| [OddLift.lean](Sarkozy/OddLift.lean), [OddTarget.lean](Sarkozy/OddTarget.lean) | Prime-coordinate first differences, arbitrary-depth free-digit lifts, CRT multiplicities, and exact moments. |
| [Binary.lean](Sarkozy/Binary.lean), [BinaryGrowth.lean](Sarkozy/BinaryGrowth.lean), [BinaryPolicy.lean](Sarkozy/BinaryPolicy.lean) | Modulo-eight geometry, transformed branches, recursive alphabets, exact moments, growth, and final shrinking. |
| [BinaryData.lean](Sarkozy/BinaryData.lean), [BinaryRealData.lean](Sarkozy/BinaryRealData.lean), [RecordBinaryTarget.lean](Sarkozy/RecordBinaryTarget.lean) | Exact full-record policy, rational-to-real proof, seed/vector checks, and binary target from row/depth numerical inequalities. |
| [BinaryRows.lean](Sarkozy/BinaryRows.lean), [BinaryDepth.lean](Sarkozy/BinaryDepth.lean) | All 25 binary growth inequalities and the fixed-depth inequality, proved by exact log/power certificates. |
| [TwoOddTarget.lean](Sarkozy/TwoOddTarget.lean) | Full target from only two expanded odd certificates; the binary component is unconditional. |
| [OddCertificate.lean](Sarkozy/OddCertificate.lean), [OddFiniteCertificate.lean](Sarkozy/OddFiniteCertificate.lean), [ActualOddTarget.lean](Sarkozy/ActualOddTarget.lean) | Finite relation reflection and transport of fixed integer witness data. |
| [OddOrder.lean](Sarkozy/OddOrder.lean), [OddOrderCertificate.lean](Sarkozy/OddOrderCertificate.lean), [OddOrder215.lean](Sarkozy/OddOrder215.lean) | Compressed predecessor-mask soundness and every edge of the actual 215 witness. |
| [PowerChecker.lean](Sarkozy/PowerChecker.lean), [PowerPolynomial.lean](Sarkozy/PowerPolynomial.lean), [FastPowerCertificate.lean](Sarkozy/FastPowerCertificate.lean) | Exact Taylor/logarithm enclosures and the shared natural-number checker for both odd witnesses. |
| [Odd215MomentData.lean](Sarkozy/Odd215MomentData.lean) | All 1,861 actual 215 power certificates, using the shared checker. |
| [OddMoments.lean](Sarkozy/OddMoments.lean), [Odd215Moment.lean](Sarkozy/Odd215Moment.lean), [Odd215Certificate.lean](Sarkozy/Odd215Certificate.lean) | Histogram transport, the actual 215 moment, and its complete expanded alphabet. |
| [OddData437.lean](Sarkozy/OddData437.lean), [OddOrder437.lean](Sarkozy/OddOrder437.lean) | All 19,683 actual rows: coordinates, distinctness, interval geometry, and every required first-difference edge. |
| [Odd437MomentData.lean](Sarkozy/Odd437MomentData.lean), [Odd437Moment.lean](Sarkozy/Odd437Moment.lean), [Odd437Threshold.lean](Sarkozy/Odd437Threshold.lean) | All 18,908 distinct-width power bounds and the full actual 437 moment. |
| [Odd437Certificate.lean](Sarkozy/Odd437Certificate.lean), [FullTarget.lean](Sarkozy/FullTarget.lean) | Complete expanded 437 alphabet and the unconditional full exponent. |
| [OneOddTarget.lean](Sarkozy/OneOddTarget.lean) | Full exponent from one expanded 437 certificate, or only two checks on its fixed low rows. |
| [RecordTarget.lean](Sarkozy/RecordTarget.lean) | Earlier general interface to two arbitrary odd low-support certificates. |
| [QuantitativeExamples.lean](Sarkozy/QuantitativeExamples.lean) | Unconditional `6^k` elements in `[1,18^k]` and exponent `3/5`; all hypotheses proved. |
| [Examples.lean](Sarkozy/Examples.lean) | The original two- and six-element finite examples. |

## Complete finite certificates

The depth-three witnesses at prime pairs `(5,43)` and `(19,23)` contain
4,913 and 19,683 points, respectively. Kernel-checked predecessor masks
prove every required edge ordering. Exact width-histogram identities connect
the endpoint-sorted geometric rows to their numerical certificates.

The 215 witness has 1,861 distinct widths; the 437 witness has 18,908.
Two exact 1024th-power inequalities and an eighth-order logarithm bound
give rigorous power lower bounds. Only two terminal root bounds are stored. The resulting weighted sums meet
the target thresholds. Every comparison is exact: high-precision Decimal
arithmetic in the generators only proposes the integer certificates.

[Odd215Certificate.lean](Sarkozy/Odd215Certificate.lean) and
[Odd437Certificate.lean](Sarkozy/Odd437Certificate.lean) construct the complete
expanded odd alphabets without assumptions. All six prime chains and the
entire binary component are also unconditional; the latter includes all 25
growth rows and the fixed-depth inequality with logarithmic margin at least 27.

No finite-certificate, recursive-construction, free-digit-lifting, counting,
or asymptotic hypothesis remains in `record_exponent`. The smaller
human-facing `>0.758` result is not the target of this development; the older
unconditional `3/5` example remains an illustration.

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

The [official full mechanical preflight passed](https://github.com/enaslund/sarkozy-lower-bound-0.758/actions/runs/35392867341)
on 2026-09-18 for commit `e26058b55ab928e321d25318185acc69fbf62ab9`, checking
both selected theorems with Comparator, the protected Challenge audit, Lean's
kernel, and independent NanoDa replay. The
[unmodified mechanical report](verification/palomar-preflight-20260918.json)
is preserved. It applies to that exact commit; this later documentation records
the result. Palomar's own submission review and registration remain separate.

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

The cleaned source passed the complete Lean build, 76 standard-axiom
inspections, and a fresh complete direct NanoDa replay with an 8 MiB stack.
See the verification record for the exact source hashes and replay results.
The earlier 32,700-declaration NanoDa pass belongs to the preserved
`before-cleanup-20260911` snapshot. Three incomplete Comparator attempts also
belong to that earlier version; their unexplained SIGTERMs are not results
for the cleaned source. These local records establish no completed Comparator
comparison. The current hosted checks and their exact source commits are in
[Palomar mechanical preflight runs](https://github.com/enaslund/sarkozy-lower-bound-0.758/actions/workflows/palomar-preflight.yml).

The mathematical formalization is complete. Palomar registration requires the
service's mechanical verification and editorial review. Our optional
[full mechanical preflight](.github/workflows/palomar-preflight.yml) runs the
official verifier, including the protected Challenge audit and both kernels,
at a pinned pipeline revision. To attempt the separate local Comparator check,
with Go and Rust/Cargo available in the Lean environment:

```bash
./scripts/verify-comparator.sh
```

The verification scripts derive from the
[official Palomar template](https://github.com/PalomarRegistry/PalomarTemplate),
with a project-compatible exporter pin recorded in the script.
They use Landrun, require Linux with Landlock support, and fetch the pinned
verification tools. The [verification record](verification/README.md) contains
the exact revisions, logs, source hashes, and commands for this box.
The ordinary Lean build needs neither Go nor Rust.

The [ordinary CI workflow](.github/workflows/ci.yml) provides the Lean build,
axiom inspection, and local Comparator setup. Both it and the official
preflight are manual (`workflow_dispatch`). The official preflight uses
`mode: full`; its mechanical report records the precise verdict and source SHA.
It is predictive preparation, not a Palomar submission.
[SUBMISSION.md](SUBMISSION.md) gives the workflow commands and submission fields.

The source and papers are published in this repository; nothing has been
submitted to or registered with Palomar. The [Apache-2.0 license](LICENSE)
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
elan toolchain install leanprover/lean4:v4.32.0
lake exe cache get
./scripts/build-sequential.sh
```

The initial downloads need network access. Cached builds work locally.
For VS Code, open this folder from a shell with `env.sh` sourced and use
the official Lean 4 extension.
