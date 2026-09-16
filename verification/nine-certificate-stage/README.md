# Local verification, 2026-09-10

The submission package with four statement declarations passes the checks below.
These are local results, not a Palomar submission or registration. The former
finite-stage logs are preserved in `finite-stage/` as historical records.

| Check | Result | Evidence |
|---|---|---|
| `lake build` | Passed. The four warnings are Challenge's deliberate statement placeholders. | [build.log](build.log) |
| `lake env lean Check.lean` | All 15 checked declarations use only `propext`, `Classical.choice`, and `Quot.sound`. | [axioms.log](axioms.log) |
| `./scripts/verify-comparator.sh` | Challenge/Solution comparison passed; both NanoDa and Lean's kernel accepted the solution. Exit status 0. | [comparator.log](comparator.log) |
| Metadata validation | Passed the upstream v0.4 JSON schema and the listed additional Palomar checks, including source types and declaration coverage. | [metadata.log](metadata.log) |
| Package layout | Source-only snapshot, exact dependency pins, unchanged Apache license, compact Mathlib-only Challenge. | [package-check.log](package-check.log) |

Comparator checked `SarkozySubmission.finite_construction`,
`SarkozySubmission.interval_moment_bound`,
`SarkozySubmission.conditional_improved_bound`, and
`SarkozySubmission.unconditional_example`, including their complete proof
dependencies. The third concludes the exponent `0.75806746` from nine finite
interval certificates; their geometry and moment inequalities remain explicit
hypotheses. No word-selection or asymptotic assertion is assumed.

The unconditional exponent `3/5` is now also a Comparator target. Separate
agents reviewed the stopping-word proof, the all-N interpolation, the target
statement, and the submission package; no mathematical issue was identified.
The metadata source type and principal-statement coverage were corrected
during this preparation. The JSON witnesses and their translation into the
expanded alphabet hypotheses were not formally checked. Existence of a tuple
satisfying all nine target hypotheses is not proved.

[snapshot.json](snapshot.json) records the checked source hashes, tool revisions,
and results. The log files preserve the actual command output. The metadata
check used PyYAML and fastjsonschema against the schema hash recorded in its
log, together with targeted checks of the current
[Palomar policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
It is not an implementation of Palomar's full validation or editorial review.
Dependency
downloads, build caches, and proof exports are not part of the saved artifact.

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
