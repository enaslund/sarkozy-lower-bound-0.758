# Lean cleanup and size

Measured 2026-09-14. These sizes cover this project's Lean source, excluding
Mathlib, toolchains, build caches, documentation, and archived copies.

| Source | Before cleanup | After cleanup |
|---|---:|---:|
| Bytes | 32,409,807 | 10,497,588 |
| Lines | 220,131 | 178,547 |
| Lean files | 147 | 148 |

The source is **67.6% smaller**. Selected compiled data artifacts also shrink
from 505,637,612 to 50,333,766 bytes; this measures 46 changed `.olean` and
generated C files, excluding dependencies and other build products. Most savings shorten large certificate literals;
they do not remove mathematical arguments. The additional file holds a shared
checker used by both odd witnesses. Generated modules contain 96.9% of the
source bytes.

Of the current total, 86 generator-owned data and chunk modules account for
10,168,796 bytes and 171,457 lines, including their small proof templates.
The other 62 files occupy 328,792 bytes and 7,090 lines. Those include the
general proof, handwritten numerical certificates, interfaces and audit files.
[Solution.lean](Solution.lean), the submission entry point, is 51 lines.

The principal changes are:

- Store sparse masks using exact hexadecimal literals and shifts. The two
  large ordering-data files shrink from 15.95 MB to 6.01 MB.
- Share the proved integer power checker in
  [FastPowerCertificate.lean](Sarkozy/FastPowerCertificate.lean). Retain only
  two terminal root bounds per row, and prove their validity using two exact
  1024th-power comparisons. A generic soundness theorem connects these tests
  to the real-power bound. This removes eighteen intermediate integers per
  row and saves a further 9.93 MB over the initial cleanup.
- Mark proof-only data `noncomputable` to suppress unused executable code.
  This preserves their definitions and ordinary kernel reduction.
- Reuse the word-moment factorization, simplify real-power identities, and
  remove redundant submission wrappers. Construction and conditional results remain.
- Provide [build-sequential.sh](scripts/build-sequential.sh), with the nine
  successful build/audit commands. The development CI and local Comparator
  launcher use it to check the heavy components separately. Hosted CI was
  untested at the September 14 measurement date; later official hosted passes
  are recorded in [verification/README.md](verification/README.md).

All 20,769 numerical rows preserve their widths, multiplicities, lower
numerators, initial scalings and final root bounds. All new integer power
and logarithm comparisons pass an independent exact-value audit. Every
shifted ordering mask was expanded and compared too.
The updated generators reproduce the changed data files. These comparisons
support the cleanup review; they do not replace Lean checking.

## What is certified

The full result in [Solution.lean](Solution.lean) is unchanged: for every
real epsilon greater than zero and every sufficiently large natural N,
there is a finite set of distinct integers in [1,N], with no nonzero square
difference, of cardinality at least N^(0.75806746 - epsilon).

All nine components and the construction and asymptotic passage are included.
The September 11 build, 79 axiom inspections, and independent NanoDa replay
of 32,700 declarations apply to the preserved version
in [verification/before-cleanup-20260911](verification/before-cleanup-20260911/).
Its theorem depends only on Lean's standard `propext`, `Classical.choice`,
and `Quot.sound`, with no computational axiom or `native_decide`.
See [SEMANTIC-AUDIT.md](SEMANTIC-AUDIT.md) for the statement and dependency review.

**The separate September 14 cleaned Lean build and all 76 axiom inspections passed.**
Its independent NanoDa replay also passed: **32,704 declarations**,
with no errors and only the three standard axioms. Both replay counts cover
the selected Solution declarations and their transitive dependencies;
original-row interfaces are covered by the full build and axiom audit. See the
[complete verification record](verification/README.md). Its frozen
source hashes are in [cleanup-source.json](verification/cleanup-source.json).
Completed build phases are recorded in
[cleanup-build/results.json](verification/cleanup-build/results.json).
The first cleanup reached 20.43 MB; its full build had one histogram process
terminated with SIGTERM without a Lean proof error. Its incomplete build and
source hashes are preserved in [intermediate-cleanup](verification/intermediate-cleanup/).
The final build runs the heavy histogram checks as separate stages.
Historical records describe their named source snapshots; the fresh checks
are bound to the final endpoint-only sources.

## Further simplification

The [encoding experiment](verification/cleanup-endpoint-benchmarks.md)
compared supplied ladders, roots reconstructed by Lean, and terminal bounds
checked by integer powers. In a 128-row sample, reconstruction was slower
and used more memory; the adopted terminal-bound format was faster and
smaller. These are sample timings, not full-project speedup claims. The
generic new soundness theorem also passed independent NanoDa checking.

Ordinary proof deduplication can still improve readability, but will have
little effect on the total size. Substantial further reductions require a
smaller certificate or a more compact representation of its numerical data.
Any such change should be assessed for kernel checking time and memory as
well as source size. Replacing a supplied witness with an expensive kernel
calculation can shorten a file while making verification harder to run.
