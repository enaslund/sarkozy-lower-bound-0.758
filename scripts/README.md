# Build and verification scripts

Run `./scripts/build-sequential.sh` from the repository root with the pinned
Lean environment available. It builds the heavy certificate targets in
sequence, completes the project build, and prints the axiom audit.
`verify-comparator.sh` prepares and runs the pinned combined verifier; see
[SUBMISSION.md](../SUBMISSION.md) for its current status.

The Python witness-generation scripts are retained for provenance and future
research. Some expect the original `research-notes/` inputs and the
`lean-formalization/` directory layout in the
[working repository](https://github.com/enaslund/sarkozy-lower-bound).
Use that working checkout for regeneration unless you adapt their input and
output paths. They are not invoked by the Lean build: the generated data and
their proved checks are already included in `Sarkozy/`.

The self-contained paper certificate programs are under `papers/` and run
without the working repository.
