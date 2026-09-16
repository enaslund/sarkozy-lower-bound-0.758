# Local verification, 2026-09-11

This extension proves eight components for the full exponent `0.75806746`:
all six prime chains, the complete binary component, and the full 215 witness,
including their numerical moments. The strongest theorem fixes the actual
19,683-row 437 witness and assumes only its edge ordering and width moment.
Its geometry is proved. Nothing has been submitted to Palomar.

| Check | Coverage | Evidence |
|---|---|---|
| `lake build` | Entire library, including the strongest fixed-row theorem and all concrete odd-data checks. Two Challenge placeholders are deliberate. | [build.log](build.log) |
| `lake env lean Check.lean` | Standard-axiom inspection of the selected general, numerical, construction and end-to-end theorems. | [axioms.log](axioms.log) |
| Cached pinned Comparator | Two Challenge/Solution declarations, including the full target from one expanded 437 certificate; NanoDa and Lean replay enabled. | [comparator.log](comparator.log), [run result](comparator-run.json) |
| Metadata | Cached upstream v0.4 schema and the explicitly listed mechanical checks. | [metadata.log](metadata.log) |
| Source/package checks | Proof-hole scan, exact dependency pins, declaration coverage and local links. | [package-check.log](package-check.log) |

See [snapshot.json](snapshot.json) for the actual results and source hashes.
The records are local mechanical verification, not an official Palomar review.

The two Comparator entries are `SarkozySubmission.interval_moment_bound` and
`SarkozySubmission.reduced_improved_bound`. The latter assumes only the 437
expanded alphabet. Its exported proof includes all eight discharged components,
including every 215 edge-order and moment check and all binary numerical checks.

The stronger `Sarkozy.record_exponent_of_437_checks` fixes the actual low rows
and proves their geometry and expansion. This interface and the unary 437
checks are included in the complete Lean build and axiom audit; they are not
separate Comparator entries. The proved 437 scalar threshold alone does not
establish its width moment. No complete 437 witness is yet claimed in Lean.

The arithmetic uses ordinary `decide` and `decide +kernel`. Both produce
proofs checked by Lean's kernel; no `native_decide` or custom axiom is used.
Generators propose exact data, but are not trusted by the Lean proofs.
Large 437 data definitions are marked `noncomputable` only to avoid unused
native code generation. Their literal values still reduce in the kernel;
the marker introduces no additional axiom.

Earlier records are preserved in `finite-stage/`, `nine-certificate-stage/`,
`three-certificate-stage/`, and `seven-component-stage/`. Their logs apply to the recorded versions,
not to later source changes. Hosted CI has not been run.

For this run, the already installed pinned executables were used directly,
with Landrun enabled, to avoid fetching unchanged tools. The equivalent
cached invocation after `source env.sh` is:

```bash
export COMPARATOR_LEAN4EXPORT=/tmp/sarkozy-palomar-tools/verification/lean4export/.lake/build/bin/lean4export
export COMPARATOR_NANODA=/tmp/sarkozy-palomar-tools/verification/nanoda/target/release/nanoda_bin
export COMPARATOR_LANDRUN=/tmp/sarkozy-palomar-tools/verification/bin/landrun
lake env /tmp/sarkozy-palomar-tools/verification/comparator/.lake/build/bin/comparator comparator.json
```

The launch script follows the current official submission service with these pins:

| Tool | Revision |
|---|---|
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| lean4export | `4e7915201d3f9f04470d9eae002fa695f7cdc589` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

The project and its exporter use Lean 4.32.0. The pinned Comparator executable
itself builds with Lean 4.34.0-rc1; this does not change the project's toolchain.
The generated 215 order checks form a sequential chain of 39 modules, each
covering at most 128 rows. This bounds peak checking memory and retains
completed work across interrupted builds. The prepared CI jobs allow 120
minutes for fresh certificate builds and replay; hosted execution is untested.

Go 1.27.1 and Rust 1.98.1 were installed under `/tmp/sarkozy-palomar-tools` to
build the verification tools. Landrun's sandbox remained enabled.

The prepared GitHub workflow uses action revisions from PalomarTemplate
commit `128a6c5ce5f48622e69927ccd639cbff401022e8`. It has not been run on
GitHub. The exported standalone repository is intended to use this folder
as its root; its license does not relicense the surrounding research archive.

To repeat the exact setup on this box while those temporary tools remain,
run from `lean-formalization/`:

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
