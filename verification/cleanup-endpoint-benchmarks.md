# Endpoint certificate simplification: proof and benchmark

This records the isolated experiment before integration. The adopted checker
is now in [FastPowerCertificate.lean](../Sarkozy/FastPowerCertificate.lean);
complete-result verification is recorded separately in [README.md](README.md).
The source sizes and future-tense integration notes below describe the
experiment at the time it was run.

The endpoint-only alternative succeeded. Its generic analytic soundness theorem is proved in Lean and independently checked by the pinned NanoDa verifier: **27,606 declarations, no errors**, with only `propext`, `Classical.choice`, and `Quot.sound`. The complete generic proof replay took 20.64 seconds at an 8 MiB stack limit. This establishes the replacement checker's mathematical soundness; integration with the full Sarkozy theorem remains separate.

The clean shared module ready for integration is `FastPowerCertificate-proposed.lean`. Its compiled/audited counterpart `EndpointCertificate.lean` differs only by two `#print axioms` commands. It provides the coordinated `EndpointCertificate`, `EndpointValid`, `endpoint_valid_sound`, `MomentEntry`, and `MomentEntry.scaled` interfaces.

## The two experiments

Each variant checks the first 128 rows of the 437 witness; preliminary 1- and 4-row versions also passed. All finite checks use ordinary `decide +kernel`, followed by independent NanoDa replay with its strict three-axiom allowlist.

| 128-row variant | Lean wall time / peak RSS | NanoDa wall time / peak RSS |
|---|---:|---:|
| Explicit 20-value root ladders | 3.50 s / 1.04 GB | 1.45–1.50 s / 192 MB |
| Compute floor/ceiling root ladders | 12.22 s / 2.02 GB | 10.11–12.24 s / 1,267 MB |
| Keep only the two terminal roots | 2.11 s / 0.835 GB | 0.28–0.50 s / 37 MB |

NanoDa memory values come from a fresh small launcher; earlier measurements included transient inherited launcher memory. Timings vary with shared machine activity, and do not establish a full-project speedup. All individual jobs stayed below the 60-second limit.

Computing every square root is correct and feasible for the sample, but moves 415,380 root calculations into kernel reduction across the full data. A generic recurrence proof is unnecessary for correctness and might improve its performance, but was not developed because the endpoint-only alternative performed better.

The endpoint-only alternative checks

```
lo^1024 <= a0 * D^1023
b0 * D^1023 <= hi^1024
```

alongside positivity, `lo, hi <= D`, and the unchanged exact polynomial logarithm comparison. It retains the original final roots, width, multiplicity, and proposed lower numerator. Its finite exported dependency closure has 567 declarations, versus 630 for supplied ladders and 649 for reconstructed ladders.

## Why the new check proves the same numerical bound

The generic theorem works with arbitrary natural `n`, using degree `n+1` and `D^n`. Dividing the two integer power comparisons by positive powers of `D` and applying the logarithm gives

```
(n+1) * log(lo/D) <= log(a0/D)
log(b0/D) <= (n+1) * log(hi/D).
```

The existing eighth-order logarithm enclosures and `PowerPolynomial.log_comparison_of_nat` put `log(hi/D)` below `(p/q) * log(lo/D)`. Combining these inequalities and applying the monotonicity of logarithm gives

```
b0/D <= (a0/D)^(p/q).
```

Every step above is Lean-proved in the proposed module. There are no new axioms, `sorry`, or native evaluation shortcuts in that proof.

## Size and remaining integration

The existing two odd moment witnesses contain 20,769 rows and 415,380 explicit root values. Independent Python reconstruction using exact integer square roots reproduced every value. Keeping only each row's terminal low/high values removes **9,933,901 bytes** from the current row text under the proposed five-argument constructor, before the small shared proof/interface changes. This would reduce the current 20.43 MB project to approximately **10.50 MB**.

The finite comparative benchmark copies the exact natural-number checker definitions into a minimal-import module. The generic analytic proof uses the real project imports; it compiled successfully in 8.42 seconds with peak RSS 6.51 GB. An initial conservative-memory-cap import attempt and a subsequently corrected cast error are retained in scratch logs, and are not successful verification records.

No frozen project source or generator was edited by this task. The next step is to integrate the shared module and endpoint data, rebuild the affected moment certificates, and replay the complete final theorem. This scratch result must not be presented as a completed verification of that later integration.

[cleanup-endpoint-benchmarks.json](cleanup-endpoint-benchmarks.json) records commands, results, source/export/tool hashes, source-size measurements, all-value reconstruction counts, and the successful generic proof replay. The original scratch sources, scripts, logs and exports are retained at `/tmp/sarkozy-sqrt-benchmark-20260914` on the research machine; those temporary files are not part of the standalone package.
