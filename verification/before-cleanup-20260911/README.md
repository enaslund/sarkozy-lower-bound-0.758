# Local verification, 2026-09-11

This version proves the full exponent `0.75806746` without finite-certificate
hypotheses. All nine components, including both odd orderings and numerical
moments, are formalized. Nothing has been submitted to Palomar.

| Check | Coverage | Evidence |
|---|---|---|
| `lake build` | Entire library, including the strongest fixed-row theorem and all concrete odd-data checks. Two Challenge placeholders are deliberate. | [build.log](build.log) |
| `lake env lean Check.lean` | Standard-axiom inspection of the selected general, numerical, construction and end-to-end theorems. | [axioms.log](axioms.log) |
| Direct pinned NanoDa | Complete Solution export for both selected declarations and their dependencies; passed with an 8 MiB stack. | [log](separate-kernel-replay/nanoda.log), [result](separate-kernel-replay/nanoda-result.json) |
| Pinned Comparator | Unresolved: two combined attempts and one separate Comparator/Lean attempt ended with SIGTERM before a final report. | [latest log](separate-kernel-replay/comparator_lean.log), [latest result](separate-kernel-replay/comparator_lean-result.json) |
| Metadata | Cached upstream v0.4 schema and the explicitly listed mechanical checks. | [metadata.log](metadata.log) |
| Source/package checks | Proof-hole scan, exact dependency pins, declaration coverage and local links. | [package-check.log](package-check.log) |

See [snapshot.json](snapshot.json) for the actual results and source hashes.
The records are local mechanical verification, not an official Palomar review.
The full library build and all 79 standard-axiom inspections passed. Direct
pinned NanoDa also passed on the complete exported Solution dependencies,
including the full unconditional numerical theorem, with an 8 MiB process stack.
The receipts bind that check to the recorded Lean sources and export hash.
NanoDa checked **32,700 declarations** with no typechecker errors and exited
with status zero. The raw log also records `Unable to print axioms`: optional
axiom printing was requested without an output destination. This occurs after
all typechecking and does not weaken the strict axiom allowlist. The
[display diagnostic](nanoda-display-diagnostic.json) records the configuration
and pinned-source checks establishing that distinction.

Current Comparator verification remains **unresolved**. Two combined attempts
and a separate attempt with temporary `enable_nanoda: false` ended with SIGTERM
before a final success report. These attempts establish neither a completed
fresh Comparator/Lean replay nor a completed Comparator statement-comparison
pass for this version. The repository's `comparator.json` remains
`enable_nanoda: true`. A successful configured Comparator run and hosted
verification remain operational requirements before claiming submission readiness.

Direct NanoDa ran inside the execution tool's existing OS sandbox, without
an additional Landrun layer. Comparator used its normal Landrun launcher.
All verification binaries were unchanged. The NanoDa pass and ordinary Lean
build do not constitute a successful combined Comparator or official service run.

The two Comparator entries are `SarkozySubmission.interval_moment_bound` and
`SarkozySubmission.improved_bound`. The latter has no certificate hypotheses.
Its exported proof includes all nine discharged components: both complete odd
witnesses, the six prime chains, and every binary numerical check.

The original packed-coordinate row interfaces and their moments are also
included in the complete Lean build and axiom audit. They are supporting
theorems rather than separate Comparator entries. Both endpoint-sorted width
histograms are checked against the corresponding geometry in the exported proof.

The arithmetic uses ordinary `decide` and `decide +kernel`. Both produce
proofs checked by Lean's kernel; no `native_decide` or custom axiom is used.
Generators propose exact data, but are not trusted by the Lean proofs.
For the 437 endpoint ordering, the exported proof uses a Boolean adjacency
check and a generic soundness theorem. A direct decision of the 19,683-element
`IsChain` proposition passed Lean but overflowed NanoDa's 8 MiB main-thread
stack. The Boolean proof checks the same comparisons without constructing that
deep decidability proof. The original direct theorem remains a supporting Lean
result; the submission uses the replacement.
The 437 width-histogram identity likewise uses Boolean list equality and the
proved `LawfulBEq` soundness interface. This replaces a recursive decidable
equality proof while preserving the exact multiset identity. Targeted
[ordering diagnostics](437-order-replay-diagnostics.json) and
[moment diagnostics](437-moment-replay-diagnostics.json) record the investigation;
these partial probes are separate from the complete direct NanoDa replay.
The separate [data audit](437-data-audit.log) records reconstruction and
independent integer checks; [generator reproducibility](437-moment-repro.json)
records byte-identical regeneration of all 437 moment certificate modules.
The [order-generator receipt](437-order-repro.json) records the corresponding
byte-for-byte regeneration of all 24 order data and proof files.
Large 437 data definitions are marked `noncomputable` only to avoid unused
native code generation. Their literal values still reduce in the kernel;
the marker introduces no additional axiom.

Earlier records are preserved in `finite-stage/`, `nine-certificate-stage/`,
`three-certificate-stage/`, `seven-component-stage/`, and `eight-component-stage/`. Their logs apply to the recorded versions,
not to later source changes. Hosted CI has not been run.
The initial unconditional replay's stack overflow and subsequent cancellation
are preserved in `full-result-initial-replay/`, with its source hashes.
After the Boolean proof changes, two combined fixed-source attempts ended
with SIGTERM (exit 143) before their final success report. Their records are
in `full-result-interrupted-replay/` and `full-result-isolated-interrupted-replay/`.
The separate Comparator/Lean attempt also ended with exit 143; its record is
in `separate-kernel-replay/`. None is counted as a pass. No runner timeout,
cancellation request or proof error was recorded for these three attempts;
the cause of termination is unconfirmed.

The complete direct NanoDa run used byte-identical hard links to the pinned
binaries. Its receipt identifies the command, configuration and source hashes;
[the export receipt](separate-kernel-replay/export-result.json) records the
complete target list and Solution export hash. No verifier code was changed.

The standard combined invocation remains available after `source env.sh`:

```bash
export COMPARATOR_LEAN4EXPORT=/tmp/sarkozy-palomar-tools/verification/lean4export/.lake/build/bin/lean4export
export COMPARATOR_NANODA=/tmp/sarkozy-palomar-tools/verification/nanoda/target/release/nanoda_bin
export COMPARATOR_LANDRUN=/tmp/sarkozy-palomar-tools/verification/bin/landrun
ulimit -s 8192
lake env /tmp/sarkozy-palomar-tools/verification/comparator/.lake/build/bin/comparator comparator.json
```

This is the configured combined check; it has not completed successfully for
the current version.

The launch script follows the current official submission service with these pins:

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
completed work across interrupted builds. The prepared CI jobs allow 350
minutes for fresh certificate builds and replay; hosted execution is untested.

During this extension, the grouped 437 ordering checks took 21 minutes 37
seconds on this box, after the data module (391 seconds) and basic geometry
checks (103 seconds) had built. The two 19,683-row width-histogram identities
took 112 and 101 seconds. These are observed wall times under a concurrent
workload, not portable benchmarks. The complete direct NanoDa replay's duration
is recorded in its result linked above.

Go 1.27.1 and Rust 1.98.1 were installed under `/tmp/sarkozy-palomar-tools` to
build the verification tools. Landrun remained enabled for Comparator;
direct NanoDa used the execution tool's existing OS sandbox.

The prepared GitHub workflow uses action revisions from PalomarTemplate
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
