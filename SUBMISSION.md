# Palomar submission preparation

The proposed entry combines the **general interval-moment criterion for
square-difference-free integer sets** with its unconditional application to
exponent **0.75806746**. All nine construction components and their numerical
checks are formalized. The numerical statement has no finite-certificate
hypotheses. See [README.md](README.md), [PROOF.md](PROOF.md), and
[PALOMAR-READINESS.md](PALOMAR-READINESS.md).

**Verified candidate:** `e26058b55ab928e321d25318185acc69fbf62ab9` passed the
[official full preflight](https://github.com/enaslund/sarkozy-lower-bound-0.758/actions/runs/35392867341)
on 2026-09-18, including both selected theorems and both kernels. The exact
[mechanical report](verification/palomar-preflight-20260918.json) is preserved.
Later revisions update the manuscripts, filenames, metadata locations, and
documentation; they are not included in that checked commit. Use the latest
pushed commit to include these manuscript revisions, and record its exact SHA.
The Lean sources and build/verification configuration remain unchanged.

## Public repository and submission fields

The substantive development is in
[enaslund/sarkozy-lower-bound-0.758](https://github.com/enaslund/sarkozy-lower-bound-0.758),
on default branch `master`, with the Lean project at repository root.
[PUBLICATION.md](PUBLICATION.md) records its source import and later manuscript
and submission-preparation changes. The original verification receipts are
preserved; the 152 frozen Lean source/configuration files are unchanged.

| Submission field | Value |
|---|---|
| Repository | `enaslund/sarkozy-lower-bound-0.758` |
| Verified revision | `e26058b55ab928e321d25318185acc69fbf62ab9` |
| Project path | **Leave blank** for repository root; literal `.` is rejected |
| Comparator configuration | `comparator.json` |
| Metadata | Default `formalization.yaml`; no override needed |
| Challenge / Solution modules | `Challenge` / `Solution` |

One configuration selects both declarations in namespace `SarkozySubmission`:

- `interval_moment_bound`: the general asymptotic criterion;
- `improved_bound`: the unconditional full exponent `37903373/50000000`.

The root [Apache-2.0 licence](LICENSE) applies to this repository's original
Lean code, documentation, both papers in source and PDF form, certificate
programs, and generated data. [NOTICE](NOTICE) records attribution.
Eric Naslund is the author and responsible maintainer; contact
[naslund.math@gmail.com](mailto:naslund.math@gmail.com).

## Run the official full mechanical preflight

The candidate above already passed. For a later revision, commit and push it,
record `git rev-parse HEAD`, then start the manual workflow:

```bash
gh workflow run palomar-preflight.yml --repo enaslund/sarkozy-lower-bound-0.758 --ref master
gh run list --repo enaslund/sarkozy-lower-bound-0.758 --workflow palomar-preflight.yml --limit 5
```

The workflow verifies the immutable `${{ github.sha }}` selected by that
dispatch. Confirm that it equals the candidate's `git rev-parse HEAD`.
Inspect the run and download its report, replacing `RUN_ID` with the run number:

```bash
gh run view RUN_ID --repo enaslund/sarkozy-lower-bound-0.758
gh run download RUN_ID --repo enaslund/sarkozy-lower-bound-0.758 --dir /tmp/sarkozy-palomar-report
```

The [workflow](.github/workflows/palomar-preflight.yml) calls
PalomarSubmission `3561d237dcc4b28482558ad28a64d767d7cc8615` with `mode: full`.
The `uses` SHA and `pipeline_commit` must remain identical. The recorded
authorization relationship is Eric Naslund's responsibility for this
substantive development; a different submitter must give their actual basis.
No secrets are passed to the reusable verifier.

This performs the protected canonical-Challenge audit, Comparator statement
comparison, Lean kernel checking, and independent NanoDa replay. The
`mechanical-report.json` artifact binds the verdict to the exact source SHA and
tool revisions. `mode: preflight` only checks preparation and must not be used
as evidence of checked proofs. The current
[workflow history](https://github.com/enaslund/sarkozy-lower-bound-0.758/actions/workflows/palomar-preflight.yml)
is the place to inspect hosted results.

The preserved local results comprise the full Lean build, 76 standard-axiom
inspections, and a direct NanoDa replay of 32,704 declarations; see
[verification/README.md](verification/README.md). Those results are not a
completed Comparator comparison. The separate `ci.yml` workflow and
`scripts/verify-comparator.sh` remain useful for development.

The official reusable preflight is recommended preparation. Palomar does not
require authors to run repository CI, and even a successful preflight does not
replace the service's required mechanical run or initiate editorial review.

## Submit and review

1. Check the final statements, abstract, source relationships, licences, and
   authorship in the candidate commit. Inspect any preflight findings.
2. Open [the Palomar submission portal](https://submit.palomar-registry.org/)
   and use the fields above. Prove repository write access and declare that
   you are a responsible author/maintainer or have approval from one.
3. Keep the private status link. The service runs mechanical verification and
   then automated editorial review. Inspect its reports before making the
   separate registration decision.

For agent-assisted submission, first read the portal's `llms.txt`; preparation
and GitHub preflight are not a portal submission. Registration publishes the
record and redacted review and preserves the pinned source permanently.

The repository records AI assistance and agent review, not human peer review
or source-author endorsement. Mechanical success does not establish novelty,
research interest, or Palomar registration. The
[pinned submitter policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/CONTRIBUTING.md)
and the current service policy govern the eventual submission.
