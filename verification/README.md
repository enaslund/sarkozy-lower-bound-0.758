# Verification records

The September 18 submission preparation adds the
[official full mechanical preflight](../.github/workflows/palomar-preflight.yml).
Its [hosted runs and mechanical-report artifacts](https://github.com/enaslund/sarkozy-lower-bound-0.758/actions/workflows/palomar-preflight.yml)
record the verdict for each exact source commit. This optional preflight runs
Palomar's protected Challenge audit and both kernels but does not submit or
register the project. [PALOMAR-READINESS.md](../PALOMAR-READINESS.md) records
the current policy assessment. The local evidence below remains historical and
is not rewritten to stand for a later hosted run.

## Local verification after cleanup, 2026-09-14

The full exponent `0.75806746` is proved without certificate hypotheses.
The cleanup preserves the two selected theorem statements and all geometric rows, widths, multiplicities and certified lower bounds. Nothing has been submitted to Palomar.

The public export on 2026-09-16 preserves these verification results and all
152 frozen Lean source/configuration files byte for byte. The original
`snapshot.json` describes the pre-publication tree, including its then-current
documentation. Documentation, license-scope clarification, paper additions
and the manual CI trigger are recorded in [public-export.json](public-export.json)
and [PUBLICATION.md](../PUBLICATION.md). No new build or replay is claimed merely
from copying the verified sources.

| Check | Coverage | Evidence |
|---|---|---|
| `lake build` | Fresh complete library build, including original-row interfaces and all concrete certificates. Two Challenge placeholders are deliberate. | [build.log](build.log) |
| `lake env lean Check.lean` | 76 standard-axiom inspections, including both selected results and the shared power-checker soundness theorem. | [axioms.log](axioms.log) |
| Direct pinned NanoDa | Fresh complete Solution export for both selected declarations and their dependencies; passed with an 8 MiB stack. | [cleanup replay](cleanup-kernel-replay/) |
| Pinned Comparator | No successful complete run for the cleaned source is established. | See the version distinction below. |
| Metadata | Cached upstream v0.4 schema and the listed mechanical checks. | [metadata.log](metadata.log) |
| Source/package checks | Proof-hole scan, exact pins, declaration coverage and local links. | [package-check.log](package-check.log) |

To repeat the nine build and axiom-audit commands in
`cleanup-build/results.json`, run from the project root:

```bash
./scripts/build-sequential.sh
```

The [script](../scripts/build-sequential.sh) finishes the seven large targets
sequentially before the complete build and audit. It requires the ordinary
Lean environment and stops at the first failed command.

[snapshot.json](snapshot.json) binds these results to the verified source hashes;
[public-export.json](public-export.json) records the subsequent publication copy.
The fresh NanoDa replay checked **32,704 declarations**
with no typechecker errors and exited with status zero in
**1,248.90 seconds**. Its complete log, source and export
hashes, command and configuration are in [cleanup-kernel-replay/](cleanup-kernel-replay/).
Only `propext`, `Classical.choice` and `Quot.sound` are permitted. These are
local mechanical checks, not official Palomar review or acceptance.

## What changed, and what was checked

Lean source decreased from **32,409,807** to **10,497,588 bytes**
(**67.6%**). Factoring trailing zero bits into
natural-number shifts shortened the two order-data sources by about 62%.
Both odd witnesses now use the proved `PowerChecker.endpoint_valid_sound` in
[FastPowerCertificate.lean](../Sarkozy/FastPowerCertificate.lean). Their 20,769
distinct-width certificates retain two hexadecimal root endpoints and derive
their initial scalings from the recorded numerators. Two direct 1024th-power
inequalities replace twenty successive square comparisons per row. A new
general soundness proof links those integer tests to the same real-power
bounds. All widths, multiplicities, lower numerators and final endpoints
match the previous certificates exactly.

Large proof data, including the 215 rows, are marked `noncomputable` to avoid
unused executable code generation. The marker neither changes their values
nor prevents kernel reduction, and it adds no axiom. Ordinary `decide` and
`decide +kernel` still check the finite comparisons. The generators remain
untrusted proposals; the shared checker proves analytic soundness.

Compiled artifact changes: 46 changed data-module `.olean` and generated C files decreased from 505,637,612 to 50,333,766 bytes, a saving of 455,303,846 bytes (about 90%). This excludes dependencies and other build products.

`Solution.lean` now contains exactly the two selected declarations. Four
redundant submission wrappers were removed, while their underlying library
theorems remain. This removes four duplicate axiom-print entries; adding the
shared checker gives 76 inspections instead of 79. Small analytic proof
simplifications preserve the 39 existing theorem signatures in the affected
modules. The [semantic audit](../SEMANTIC-AUDIT.md) found no hidden premise,
weakened square-difference condition or mismatch with the intended
all-large-`N` lower bound.

## Version distinction and remaining submission checks

The previous complete NanoDa pass checked **32,700 declarations**. Its
79-declaration axiom audit, logs and source hashes are preserved in
[before-cleanup-20260911/](before-cleanup-20260911/). That pass is evidence
for the earlier version; the fresh replay above checks the cleaned source.
The prior NanoDa log's optional `Unable to print axioms` diagnostic is
explained in [nanoda-display-diagnostic.json](nanoda-display-diagnostic.json).

The initial 20.43 MB cleanup also has preserved sources and an incomplete
build under `intermediate-cleanup/`; its histogram process received SIGTERM.
The earlier `cleanup-moment-data.json` describes that intermediate ladder
encoding. The final endpoint-format comparisons, soundness experiment and
source sizes are recorded in `cleanup-endpoint-data.json`,
`cleanup-endpoint-benchmarks.json` and `cleanup-size.json`. The final build
runs four heavy histogram/interface targets separately before the complete
library build, for nine sequential build/audit phases in total.

The two combined Comparator attempts and the separate Comparator/Lean
attempt that received SIGTERM also belong to the version **before cleanup**.
Their records remain in `full-result-interrupted-replay/`,
`full-result-isolated-interrupted-replay/` and `separate-kernel-replay/`.
No runner cancellation or proof error was recorded for these three attempts;
the termination cause is unconfirmed. None is counted as a pass or as a test
of the cleaned version.

These preserved local records contain no successful current Comparator replay
and statement-comparison pass. Consult the hosted reports linked above for
subsequent official-verifier preflights. The repository's `comparator.json`
enables NanoDa; Palomar also forces it in its protected configuration.
The ordinary Lean build and separate NanoDa pass alone do not constitute a
complete configured Comparator run, hosted verification or service acceptance.

The selected entries are `SarkozySubmission.interval_moment_bound` and
`SarkozySubmission.improved_bound`. The latter has no certificate parameters;
its proof includes all nine components. Original packed-coordinate row
interfaces and their moments are supporting library theorems included in the
full build and axiom audit.

Earlier partial-stage and replay diagnostic records remain for provenance.
Their timings and generator hashes describe their recorded sources, not the
cleaned source. The 437 Boolean endpoint-order and width-histogram proofs
remain in use; their original 8 MiB stack diagnostics are in
[437-order-replay-diagnostics.json](437-order-replay-diagnostics.json) and
[437-moment-replay-diagnostics.json](437-moment-replay-diagnostics.json).

The standard combined invocation remains available after `source env.sh`:

```bash
export COMPARATOR_LEAN4EXPORT=/tmp/sarkozy-palomar-tools/verification/lean4export/.lake/build/bin/lean4export
export COMPARATOR_NANODA=/tmp/sarkozy-palomar-tools/verification/nanoda/target/release/nanoda_bin
export COMPARATOR_LANDRUN=/tmp/sarkozy-palomar-tools/verification/bin/landrun
ulimit -s 8192
lake env /tmp/sarkozy-palomar-tools/verification/comparator/.lake/build/bin/comparator comparator.json
```

This is the configured local combined check; these preserved records contain
no successful completion for the cleaned version.

The launch script uses submission-service revisions inspected on 2026-09-11:

| Tool | Revision |
|---|---|
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| lean4export | `4e7915201d3f9f04470d9eae002fa695f7cdc589` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

The [tool-integrity record](tool-integrity.json) includes local binary hashes,
the three Git revision checks, and Landrun's embedded Go module version.

The project and its exporter use Lean 4.32.0. The pinned Comparator executable
itself builds with Lean 4.34.0-rc1; this does not change the project's toolchain.
The generated order checks use 39 blocks for 215 and 154 blocks for 437,
each covering at most 128 rows. The 437 blocks are grouped into sequential
modules to reduce repeated library loading. Its 148 numerical blocks are
grouped into 19 sequential modules for the same reason. This bounds peak checking memory and retains
completed work across interrupted builds. The CI build job and Comparator launcher use `scripts/build-sequential.sh`,
which reproduces the nine locally passed commands. Shell syntax and command
order were checked; this is not a hosted CI or combined Comparator pass.
The prepared CI jobs allow 350
minutes for fresh certificate builds and replay; hosted execution is untested.

Go 1.27.1 and Rust 1.98.1 were installed under `/tmp/sarkozy-palomar-tools` to
build the verification tools. Landrun remained enabled for Comparator;
direct NanoDa used the execution tool's existing OS sandbox.

The manual GitHub workflow uses action revisions from PalomarTemplate
commit `128a6c5ce5f48622e69927ccd639cbff401022e8`. It has not been run on
GitHub. The exported standalone repository is intended to use this folder
as its root; its license does not relicense the surrounding research archive.

To install the same tools and attempt the configured combined check on this
box while those temporary tools remain, run from `lean-formalization/`:

```bash
source env.sh
export CARGO_HOME=/tmp/sarkozy-palomar-tools/cargo
export RUSTUP_HOME=/tmp/sarkozy-palomar-tools/rustup
export GOPATH=/tmp/sarkozy-palomar-tools/gopath
export GOCACHE=/tmp/sarkozy-palomar-tools/gocache
export PATH="/tmp/sarkozy-palomar-tools/go/bin:$CARGO_HOME/bin:$PATH"
export PALOMAR_COMPARATOR_CACHE=/tmp/sarkozy-palomar-tools/verification
./scripts/verify-comparator.sh
```

For a fresh machine, make Go and Rust/Cargo available, activate the project's
Lean environment, and run the same script without the temporary-directory
settings. It will fetch the pinned tools into `.cache/palomar-comparator`.
The ordinary `lake build` needs only the Lean setup in the project README.
