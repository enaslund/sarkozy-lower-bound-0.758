# Local verification, 2026-09-11

This extension proves all six prime-chain certificates and the entire binary
component for the full exponent `0.75806746`, including their numerical
inequalities. The strongest theorem still assumes the two odd low-support
certificates with geometry, ordering and moments. Nothing has been submitted
to Palomar.

| Check | Coverage | Evidence |
|---|---|---|
| `lake build` | Entire library, including the strongest low-support theorem and the preparatory odd-data checks. Five Challenge placeholders are deliberate. | [build.log](build.log) |
| `lake env lean Check.lean` | Standard-axiom inspection of the selected general, numerical, construction and end-to-end theorems. | [axioms.log](axioms.log) |
| Cached pinned Comparator | Five Challenge/Solution declarations, including the full target from only two expanded odd alphabets; NanoDa and Lean replay enabled. | [comparator.log](comparator.log), [run result](comparator-run.json) |
| Metadata | Cached upstream v0.4 schema and the explicitly listed mechanical checks. | [metadata.log](metadata.log) |
| Source/package checks | Proof-hole scan, exact dependency pins, declaration coverage and local links. | [package-check.log](package-check.log) |

See [snapshot.json](snapshot.json) for the actual results and source hashes.
The records are local mechanical verification, not an official Palomar review.

The five Comparator entries are `SarkozySubmission.finite_construction`,
`interval_moment_bound`, `conditional_improved_bound`, `unconditional_example`
and `reduced_improved_bound`. The last uses only the two odd expanded
alphabets. Thus its exported proof includes the fully discharged six prime
chains and the full binary component, including all numerical certificates.

The still stronger `Sarkozy.record_exponent_of_finite_checks` constructs the
expanded odd alphabets from their low supports. This theorem and the general
odd lift are included in the full Lean build and axiom inspection, rather
than being separate Comparator entries. The 215-data checks are preparatory:
coordinate/interval bounds and injectivity do not establish its edge ordering
or its moment. No complete odd witness is claimed to satisfy the remaining
hypotheses.

The arithmetic uses ordinary `decide` and `decide +kernel`. Both produce
proofs checked by Lean's kernel; no `native_decide` or custom axiom is used.
Generators propose exact data, but are not trusted by the Lean proofs.

Earlier records are preserved in `finite-stage/`, `nine-certificate-stage/`,
and `three-certificate-stage/`. Their logs apply to the recorded versions,
not to later source changes. Hosted CI has not been run.

For this run, the already installed pinned executables were used directly,
with Landrun enabled, to avoid fetching unchanged tools. The equivalent
cached invocation after `source env.sh` is:

```bash
export PALOMAR_LANDRUN_BIN=/tmp/sarkozy-palomar-tools/verification/bin/landrun
export COMPARATOR_LEAN4EXPORT=/tmp/sarkozy-palomar-tools/verification/lean4export/.lake/build/bin/lean4export
export COMPARATOR_NANODA=/tmp/sarkozy-palomar-tools/verification/nanoda/target/release/nanoda_bin
export COMPARATOR_LANDRUN="$PWD/scripts/landrun-wrapper.sh"
lake env /tmp/sarkozy-palomar-tools/verification/comparator/.lake/build/bin/comparator comparator.json
```

The Comparator run used scripts derived from the official template with these pins:

| Tool | Revision |
|---|---|
| Comparator | `68a064109f01c08f47c8edc9f51d6a2bbffaa188` |
| lean4export | `4e7915201d3f9f04470d9eae002fa695f7cdc589` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

The project and its exporter use Lean 4.32.0. The pinned Comparator executable
itself builds with Lean 4.33.0-rc1; this does not change the project's toolchain.
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
