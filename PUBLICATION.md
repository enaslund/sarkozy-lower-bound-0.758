# Public result repository

This repository contains the full Lean proof of exponent **0.7580758318008816**
and the two self-contained papers. Its September 2026 version, for exponent
`0.75806746`, is registered as Palomar entry PALOMAR-2026-09-19-000006,
version 1; the sections below record that version first and then the October
update. The separate
[working repository](https://github.com/enaslund/sarkozy-lower-bound) remains
the research workspace.

The source import on 2026-09-16 comes from working commit
`fe0b29937c56b77ba5dd46328db340936e8473ac`. Its standalone Lean archive was
prepared from snapshot `a825e9489f26c057b9bb8c2b57ba7049220a75e1` and matches
the tracked Lean project exactly. The new repository starts its own history.

All **148 Lean files** and the **four pinned build/verification configuration
files** match `verification/cleanup-source.json`, which also matches the
successful September 14 after-cleanup NanoDa replay record. The completed
checks are the full Lean build, 76 standard-axiom inspections and a direct
independent NanoDa replay of 32,704 declarations in the selected Solution
dependency closure, without errors. This import checks file identity;
it does not claim a new build or an additional replay.

The original verification receipts remain unchanged. The initial publication changes
are documentation, the Python-cache ignore rules, and a manual CI trigger.
At that import, the four paper deliverables and their two certificate programs
matched the copied paper verification reports. Exact import comparisons
are recorded in [verification/public-export.json](verification/public-export.json).

The Lean project is at the repository root, so leave the project-path field
blank when submitting to Palomar; a literal `.` is not accepted. The GitHub
default branch is `master`. On the
original machine the local layout is:

```text
~/src/enaslund/sarkozy-lower-bound-0.758/
├── .bare/       bare Git repository
├── .git         pointer to .bare
└── master/      working tree; run Lean and Git commands here
    ├── Solution.lean
    ├── Sarkozy/
    └── papers/
```

On 2026-09-18 Eric Naslund authorized Apache-2.0 licensing for this repository's
original work, including both papers, their sources and PDFs, certificate
programs, documentation, generated data, and the Lean formalization.
[NOTICE](NOTICE) records the scope and attribution. External cited works and
dependencies retain their own licences. The original research repository and
its Git state are unchanged.

The September 18 paper revision adds the author's email and his verbatim
AI-reading note before the mathematics, adds the licence notice, and updates
the displayed date. Mathematical text and embedded certificate programs are
unchanged. The rebuilt PDFs and their sources have new hashes, recorded in
[papers/verification/publication-20260918.json](papers/verification/publication-20260918.json).
The original paper reports remain historical evidence for the earlier files.

A subsequent manuscript revision uses the author's updated opening paragraph
and filenames based on the paper titles, with matching repository links and
metadata locations. Both introductions and bibliographies now briefly cite
Naslund's 2022 function-field paper and Jones's counterexamples registered as
Palomar entry `PALOMAR-2026-09-17-000003`, version 1. The proofs, certificate
programs, and all 152 frozen Lean source/configuration files are unchanged.
Current artifact hashes and PDF checks are in
[papers/verification/revision-20260918.json](papers/verification/revision-20260918.json).
The earlier publication and Palomar reports retain their original filenames
and hashes and apply to their recorded revisions.

Submission preparation also adds structured manuscript references, citation
metadata, and the official reusable full mechanical preflight, pinned to
PalomarSubmission `3561d237dcc4b28482558ad28a64d767d7cc8615`.
Its [manual workflow runs](https://github.com/enaslund/sarkozy-lower-bound-0.758/actions/workflows/palomar-preflight.yml)
record exact checked revisions and verdicts. Running this preflight does not
submit to or register with Palomar.

On September 19, Palomar's submission verifier passed commit
`4de015dae4f256ea9af929727f70afa8ee118c74` in
[run 35424167849](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/35424167849).
Its [public mechanical report](verification/palomar-submission-20260919.json)
is archived byte for byte. It checks both selected statements through the
protected Challenge audit, Comparator, Lean, and NanoDa. This report is
mechanical evidence for its recorded commit, not a registration record.

The subsequent metadata revision retains arXiv `math.NT` and `math.CO`, replaces
MSC2020 `03B35` with `05D05` alongside `11B75`, and expands the public abstract
to cover the general interval-moment criterion and its numerical application.
The verification scope and current documentation now distinguish the
September 11 before-cleanup replay, the separate September 14 after-cleanup
checks, the September 18 hosted preflight, and the September 19 submission run.
Original receipts remain unchanged. All 152 frozen Lean source/configuration
files retain their recorded hashes; this metadata revision is not a new build,
kernel replay, or Palomar submission.

## October 2026 update (version 2)

The October update replaces the proof and the full paper with the improved
exponent `0.7580758318008816 = 473797394875551/625000000000000`. It is
prepared as version 2 of PALOMAR-2026-09-19-000006 from this same repository,
with the same project path (repository root) and Comparator configuration.

**Lean.** The Lean project at the repository root is replaced by the project in
`lean-formalization/` of working commit `aa58ba9de353ae5a934455ed30b409f631b456b2`, copied
unchanged: all 117 `.lean` files, `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`, `comparator.json` and the scripts. Thirty-one Lean files
of the September version that no longer exist (mainly the old `(19,23)`
certificate chunks) are removed. The proof keeps every general theorem and
changes the finite witnesses, the odd interface (one digit depth per prime)
and the certificate precision. The toolchain moves from Lean 4.32.0 to
v4.35.0-rc2, Palomar's current minimum, with Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, and every file now uses the
module system. `scripts/verify-comparator.sh` now runs the toolchain's bundled
`lake comparator` with NanoDa and con-ron, as Palomar's verifier does. The
public manual-only `ci.yml` trigger is kept.

**Papers.** `papers/square-difference-free-sets-of-exponent-0.7580758318.tex`
and its PDF replace the September full paper. The research copy differs only in
the filename named in its Appendix A. Claude Opus 5.5 revised it under Eric
Naslund's supervision; its opening note says so. Its certificate program,
`papers/square-difference-free-certificate.py`, is replaced by the new one,
byte-identical to the research copy and attached to the PDF. The simpler
companion keeps its mathematics and certificate program; only its references
to the full paper (exponent, witness sizes, citation, date) change. Hashes and
build checks are in
[papers/verification/revision-20261006.json](papers/verification/revision-20261006.json).

**Records.** [verification/README.md](verification/README.md) begins with the
October records (the port and the Lean v4.35.0-rc2 rebuild, axiom audit,
kernel replays and local comparator run); the September records below it are
unchanged and apply to their recorded revisions.
`formalization.yaml`, `README.md`, `SUBMISSION.md`, `PALOMAR-READINESS.md`,
`CITATION.cff`, `PROOF.md`, `SEMANTIC-AUDIT.md` and `CLEANUP.md` describe
version 2; the preflight workflow is pinned to PalomarSubmission
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` and names the existing entry.
