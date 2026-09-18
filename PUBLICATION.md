# Public result repository

This repository contains the full Lean proof of exponent **0.75806746** and
the two self-contained papers. The separate
[working repository](https://github.com/enaslund/sarkozy-lower-bound) remains
the research workspace.

The source import on 2026-09-16 comes from working commit
`fe0b29937c56b77ba5dd46328db340936e8473ac`. Its standalone Lean archive was
prepared from snapshot `a825e9489f26c057b9bb8c2b57ba7049220a75e1` and matches
the tracked Lean project exactly. The new repository starts its own history.

All **148 Lean files** and the **four pinned build/verification configuration
files** match `verification/cleanup-source.json`, which also matches the
successful complete NanoDa replay record. The completed checks are the full
Lean build, 76 standard-axiom inspections and a direct independent NanoDa
replay of 32,704 declarations without errors. This import checks file identity;
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
