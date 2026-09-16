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

The original verification receipts remain unchanged. The publication changes
are documentation, the Python-cache ignore rules, and a manual CI trigger.
The four paper deliverables and their two certificate programs are unchanged
and match the copied paper verification reports. Exact import comparisons
are recorded in [verification/public-export.json](verification/public-export.json).

The Lean project is at the repository root, so the project directory for
future submission is `.`. The GitHub default branch is `master`. On the
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

The Lean formalization retains its Apache-2.0 license. The paper copies retain
their existing rights; this export does not assign them a new license.
The original research repository and its Git state are unchanged.

Palomar submission work is the next step. The copied verification workflow
is manual (`workflow_dispatch`); no hosted run, Palomar submission or registry
acceptance is claimed by publishing these files.
