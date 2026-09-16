# Historical finite-stage verification, 2026-09-10

This preserves the earlier finite-only result. Its source hashes identify that
earlier stage, not the current extended package. See the parent directory for
the current verification record.

The basic finite formalization passes all checks listed below. These are local
results, not a Palomar submission or registration.

| Check | Result | Evidence |
|---|---|---|
| `lake build` | Passed, including both examples. The sole warning is Challenge's deliberate statement placeholder. | [build.log](build.log) |
| `lake env lean Check.lean` | All five checked declarations use only `propext`, `Classical.choice`, and `Quot.sound`. | [axioms.log](axioms.log) |
| `./scripts/verify-comparator.sh` | Challenge/Solution comparison passed; both NanoDa and Lean's kernel accepted the solution. Exit status 0. | [comparator.log](comparator.log) |
| Metadata schema validation | Passed the upstream `formalization.yaml` v0.4 JSON schema. | [metadata.log](metadata.log) |

Comparator checked `SarkozySubmission.finite_construction`, including its
dependencies in `Sarkozy/Ranked.lean` and `Sarkozy/CRT.lean`. The examples were
checked by the ordinary Lean build and axiom inspection. They are not separate
Comparator targets. The independently delegated statement review found no
mismatch between the source's finite bound and the advertised theorem.

[snapshot.json](snapshot.json) records the checked source hashes, tool revisions,
and results. The log files preserve the actual command output. Dependency
downloads, build caches, and proof exports are not part of the saved artifact.

The Comparator run used the official template scripts with these pins:

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
