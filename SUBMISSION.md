# Palomar submission preparation (version 2)

This revision updates
[PALOMAR-2026-09-19-000006](https://palomar-registry.org/entry?id=PALOMAR-2026-09-19-000006&version=1)
from exponent `0.75806746` to **0.7580758318008816**. It keeps the **general
interval-moment criterion for square-difference-free integer sets** and its
unconditional application, now with new finite witnesses, on Lean
v4.35.0-rc2 with the module system. All nine construction components and their
numerical checks are formalized. The numerical statement has no
finite-certificate hypotheses. See [README.md](README.md), [PROOF.md](PROOF.md),
and [PALOMAR-READINESS.md](PALOMAR-READINESS.md).

**The official full preflight passed on 2026-10-07** for commit
`389566cfec3a14ace44fe554558d824310351214` in [run 37552134159](https://github.com/enaslund/sarkozy-lower-bound-0.758/actions/runs/37552134159)
(PalomarSubmission `d4e41c1d5b0d`, profile `palomar-standard-v1`, `existing_id`
PALOMAR-2026-09-19-000006): `status: pass`, `stage: complete`, no errors or
warnings. Both selected theorems passed the protected canonical-Challenge audit
and `lake comparator` with con-ron (29,813 declarations), NanoDa and Lean's
kernel, and all 117 Lean files passed the module-system and line-count check.
The [mechanical report](verification/palomar-preflight-20261007.json) is preserved;
later commits change only documentation.

## Submission fields

| Submission field | Value |
|---|---|
| Repository | `enaslund/sarkozy-lower-bound-0.758` (unchanged) |
| Revision to submit | The pushed 40-character commit SHA from `git rev-parse HEAD` |
| Existing Palomar ID | **`PALOMAR-2026-09-19-000006`** |
| Project path | **Leave blank** for repository root (unchanged); literal `.` is rejected |
| Comparator configuration | `comparator.json` (unchanged) |
| Metadata | Default `formalization.yaml`; no override needed |
| Challenge / Solution modules | `Challenge` / `Solution` |

The policy requires an update to keep the repository, project path and
Comparator configuration path of the current version; all three are unchanged.
The root configuration selects both declarations in namespace
`SarkozySubmission`:

- `interval_moment_bound`: the general asymptotic criterion (unchanged);
- `improved_bound`: the unconditional full exponent
  `473797394875551/625000000000000` (version 1: `37903373/50000000`).

Say in the submission that version 2 strengthens the numerical exponent with
new finite witnesses and moves to the current Lean toolchain; the general
criterion and its proof are unchanged. [PUBLICATION.md](PUBLICATION.md) records
the changes.

The root [Apache-2.0 licence](LICENSE) applies to this repository's original
Lean code, documentation, both papers in source and PDF form, certificate
programs, and generated data. [NOTICE](NOTICE) records attribution.
Eric Naslund is the author and responsible maintainer; contact
[naslund.math@gmail.com](mailto:naslund.math@gmail.com).

## Run the official full mechanical preflight

To rerun the optional preflight for a later revision, commit and push it,
record `git rev-parse HEAD`, then start the manual workflow on that ref:

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
PalomarSubmission `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` with `mode: full`
and `existing_id` set to this entry. It selects the approved GitHub-hosted
execution profile `palomar-standard-v1` (4 cores, 16 GB): Palomar's default
profile runs on a Namespace runner available only to Palomar's own runs. The `uses` SHA and `pipeline_commit` must
remain identical. The recorded authorization relationship is Eric Naslund's
responsibility for this substantive development; a different submitter must
give their actual basis. No secrets are passed to the reusable verifier.

This performs the protected canonical-Challenge audit and runs the toolchain's
`lake comparator`, which checks the statements and has Lean's kernel, NanoDa
and con-ron each accept the proofs. The `mechanical-report.json` artifact binds
the verdict to the exact source SHA and tool revisions. `mode: preflight` only
checks preparation and must not be used as evidence of checked proofs.

`scripts/verify-comparator.sh` runs the same bundled comparator and kernels
locally (it needs `bwrap`); the local results are in
[verification/README.md](verification/README.md). The separate `ci.yml`
workflow remains useful for development. Palomar does not require authors to
run repository CI, and a successful preflight neither replaces the service's
required mechanical run nor initiates editorial review.

## Submit and review

1. Check the final statements, abstract, source relationships, licences, and
   authorship in the candidate commit. Inspect any preflight findings.
2. Open [the Palomar submission portal](https://submit.palomar-registry.org/)
   and submit the commit as an update, entering the existing Palomar ID
   `PALOMAR-2026-09-19-000006` and the fields above. Prove repository write
   access and declare that you are a responsible author/maintainer or have
   approval from one; the existing identifier does not by itself authorise an
   update.
3. Keep the private status link. The service runs mechanical verification and
   then automated editorial review. Inspect its reports before making the
   separate registration decision.
4. If registration is offered after review, choose Register to append version 2.
   Version 1 and its source commit remain unchanged in the registry.

For agent-assisted submission, first read the portal's `llms.txt`; preparation
and GitHub preflight are not a portal submission. Registration publishes the
record and redacted review and preserves the pinned source permanently.

The repository records AI assistance and agent review, not human peer review
or source-author endorsement. Mechanical success does not establish novelty,
research interest, or Palomar registration. The
[pinned submitter policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md)
and the current service policy govern the submission.

## Version 1 record

Version 1 passed the service's
[mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/35424167849)
on 2026-09-19 for commit `4de015dae4f256ea9af929727f70afa8ee118c74` and was
registered from `e5d693729e23762b063a55015ad79ccaf28a3217`; the
[mechanical report](verification/palomar-submission-20260919.json) and the
September 18 [preflight report](verification/palomar-preflight-20260918.json)
are preserved.
