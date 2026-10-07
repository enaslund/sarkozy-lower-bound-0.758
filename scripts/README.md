# Build and verification scripts

Run `./scripts/build-sequential.sh` from the repository root with the pinned
Lean environment available. It builds the heavy certificate targets in
sequence, completes the project build, and prints the axiom audit.
`verify-comparator.sh` runs the comparator bundled with the pinned Lean
toolchain, with Lean's kernel, NanoDa and con-ron, as Palomar's verifier does;
it needs `bwrap`. `landrun-wrapper.sh` belongs to the September Comparator
setup and is kept only for the historical records in `verification/`.

The Python witness-generation scripts are retained for provenance and future
research. Some expect the original `research-notes/` inputs and the
`lean-formalization/` directory layout in the
[working repository](https://github.com/enaslund/sarkozy-lower-bound).
Use that working checkout for regeneration unless you adapt their input and
output paths. Every generator writes Lean module headers through
`lean_module.py`, and each reproduces the included Lean files byte for byte. They are not invoked by the Lean build: the generated data and
their proved checks are already included in `Sarkozy/`.

The self-contained paper certificate programs are under `papers/` and run
without the working repository.
