# Semantic audit of the full lower bound

Reviewed 2026-09-11; numerical-checker extension reviewed 2026-09-14; port to
the exponent `0.7580758318008816` reviewed 2026-10-06 (see the last section).
**No mathematical or statement-level defect was found.**
The final theorem proves the intended square-difference-free lower bound with
the full exponent `0.7580758318008816`. This is a source-level adversarial
review; fresh build and verifier results are recorded separately in
[verification/README.md](verification/README.md).

## What the theorem actually says

[`SarkozySubmission.improved_bound`](Solution.lean) has no hypotheses. Expanded
into ordinary mathematical notation, it states that for every real
\(\varepsilon>0\), there is a natural number \(N_0\) such that **every** natural
number \(N\geq N_0\) admits a finite set \(A\subseteq\mathbb Z\) satisfying

\[
 A\subseteq\{1,\ldots,N\},\qquad
 y-x\ne z^2\quad(x,y\in A,\ z\in\mathbb Z\setminus\{0\}),\qquad
 |A|\geq N^{473797394875551/625000000000000-\varepsilon}.
\]

This is the usual meaning of the lower bound
\(N^{0.7580758318008816-o(1)}\). The quantifier order permits the set and the threshold
to depend on \(\varepsilon\), as required. It establishes all sufficiently
large \(N\), rather than merely an infinite subsequence.

The numeral `(473797394875551 : ℝ) / 625000000000000` is division in **the real
numbers**, exactly `0.7580758318008816`. The base `N` and cardinality are also cast to the reals in the
size inequality. There is no natural-number division or truncated exponent.
The upper bound on set elements is an integer comparison with the cast of
`N`. Using `Finset ℤ` counts distinct integers, not a multiset.

[`SquareDifferenceFree`](Sarkozy/Ranked.lean) quantifies over both ordered
pairs of set elements and every nonzero integer root. Consequently it
excludes every positive square difference, including `1`. Zero differences
are correctly permitted. The final theorem spells out this condition rather
than relying on an ambiguously named predicate.

## Where all assumptions are discharged

The proof is
[`improved_bound`](Solution.lean) →
[`record_exponent`](Sarkozy/FullTarget.lean) → the assembled interval-moment
criterion. Earlier conditional interfaces are intermediate lemmas; they are
not assumptions of the final theorem.

| Components | Square bases | Discharging declarations |
|---|---|---|
| Six prime chains | \(3^2,7^2,11^2,31^2,59^2,103^2\) | `concretePrime_interval_ordered`, `concretePrime_geometry`, `concretePrime_certified_moment`; assembled in [ReducedTarget](Sarkozy/ReducedTarget.lean) |
| First odd component | \(215^6\), with primes 5 and 43 | `OddOrder215.interval_certificate` in [Odd215Certificate](Sarkozy/Odd215Certificate.lean) |
| Second odd component | \((19^3\cdot23^2)^2\), with three digits at 19 and two at 23 | `OddOrder437.interval_certificate` in [Odd437Certificate](Sarkozy/Odd437Certificate.lean) |
| Binary component | \(4^{10^{20}}\) | `RecordBinary.policy_valid`, `rows_verified`, `depth_condition`; assembled by `record_binary_interval_certificate` in [TwoOddTarget](Sarkozy/TwoOddTarget.lean) |

[Parameters](Sarkozy/Parameters.lean) proves that all nine bases are squares,
greater than one, and pairwise coprime. The nine moment powers are
nonnegative, and their sum exceeds the target exponent by exactly
`15468032462 / 10^25`. The strict surplus used to absorb losses is therefore
positive, not a floating-point approximation.

For each odd component, the checked ordering and positive widths imply
distinctness of the low points. The mask checker proves that every semantic
square predecessor is included; arbitrary lookup trees cannot silently omit
an edge. Equal prime-coordinate prefixes recurse independently, and
[OddLift](Sarkozy/OddLift.lean) proves that distinct free-digit copies of the
same low point cannot form a square edge. Its injective CRT encoding gives
the exact free-digit multiplicity. The certified width histogram is proved
to be a permutation of the geometry widths, so a correct numerical bound for
the wrong widths cannot be substituted.

The binary alphabet is defined recursively and verified by induction at
every depth. The depth `10^20` is an ordinary finite natural number; its
alphabet need not be explicitly enumerated. All policy validity checks,
growth rows, initialization, reflection/parity conditions and the final
depth inequality are proved. Exact integer square comparisons and proved
logarithmic bounds justify the numerical estimates.

## Construction and asymptotic passage

The general argument is also proved, not imported as a certificate:

1. [Intervals](Sarkozy/Intervals.lean) lifts ordered interval alphabets to
   square-base words. Equal low digits can be cancelled because the base is
   a square; this property is explicitly required and supplied.
2. [Stopping](Sarkozy/Stopping.lean) proves a finite stopping-word count,
   selecting a positive length and a set with a common positive lower width.
   [Moment](Sarkozy/Moment.lean) and [Growth](Sarkozy/Growth.lean) use the strict
   contribution surplus to pay for selection and rank losses.
3. [CRT](Sarkozy/CRT.lean) proves injectivity, multiplicative cardinality and
   strict rank increase for modular square edges. Ranks add across
   coordinates; at least one increases for distinct combined residues.
4. [Ranked](Sarkozy/Ranked.lean) chooses representatives in reverse rank
   order. A hypothetical positive square difference would force their
   difference to be negative. [Words](Sarkozy/Words.lean) amplifies the finite
   construction to every geometric scale.
5. [Asymptotic](Sarkozy/Asymptotic.lean) interpolates to every large natural
   `N`, then absorbs the fixed multiplicative loss into `N^ε`. Its threshold
   is at least one, avoiding any issue with zero raised to negative powers.

## Trust and scope

The recorded axiom audit for both `Sarkozy.record_exponent` and
`SarkozySubmission.improved_bound` lists only `propext`, `Classical.choice`
and `Quot.sound`, Lean's usual foundational axioms. The proved source scan
found no `sorry`, `admit`, custom axiom, `unsafe`, `native_decide`, or
`Lean.ofReduceBool`. The two intentional `sorry` declarations in
[Challenge](Challenge.lean) specify the submission challenge; `Solution`
does not import that module. They are absent from the proved theorem's
dependency chain.

The shared endpoint checker proves that two direct integer power
inequalities and the logarithm comparison imply the real-power bound. The
proof handles any positive integer degree; the current certificates use
degree 4096. Its positivity hypotheses, denominator scalings and inequality
directions were checked. The current source passed a fresh complete Lean
build and 76 axiom inspections. The independent NanoDa replay recorded in
[verification/README.md](verification/README.md) covers the September source,
not the current one.

The data generators propose witnesses. Their output is checked through
proved soundness lemmas and ordinary kernel reduction, so generator
correctness and the original JSON files are not mathematical assumptions.
The prior complete Lean build, axiom audit and independent NanoDa replay
provide machine-checking evidence for their recorded source snapshot.
Those records must not be treated as verification of later edits without
rebuilding; incomplete Comparator runs do not establish submission acceptance.

The formal result is an existence theorem. It does not claim an efficient
algorithm for producing the very large sets, an explicit practical threshold,
optimality of the exponent, or priority over the literature. Those additional
claims are not needed for the stated Sarkozy lower bound. Stale introductions
that described earlier conditional stages were corrected during this review.
The conditional lemmas remain useful modular interfaces; their inputs are
discharged in the full theorem.

## Review of the port to 0.7580758318008816 (2026-10-06)

The port changed the selected numerical statement only in its exponent
literal. `interval_moment_bound` is unchanged, and `improved_bound` differs
only in replacing `37903373 / 50000000` by `473797394875551 / 625000000000000`;
the Challenge and Solution statements were compared textually and agree. The
review checked the following points.

- **General theorems.** No theorem of the asymptotic criterion, the odd lift
  or the binary recursion changed. `odd_prime_interval_lift` already allowed a
  separate depth for each prime.
- **Odd interface.** `recordOddDepths` gives depths `(3,3)` and `(3,2)`.
  `recordOdd_modulus` and `recordOdd_free_factor` prove that the lifted
  modulus is `componentBases` and the free multiplicity is `215^3`,
  respectively `3628411 = 19^3*23^2`, by computation rather than by
  assumption. `componentBases 7 = 3628411^2` is a square greater than one and
  coprime to the other bases, as `Parameters` proves.
- **Order checker.** `sourceCheck`, `targetCheck` and
  `interval_order_of_masks` now take one depth per prime. The soundness proof
  is the same induction applied separately in each coordinate, and the
  conclusion quantifies over `PrimeLowRelated (p c) (e c)`, exactly the
  relation required by the lift. The `(5,43)` call sites pass depths `3 3`.
- **Numerical certificates.** All moment, row, threshold, chain and depth
  certificates are checked by the same proved lemmas as before, now with more
  precision. In particular the binary rows switched from square-root ladders
  to `PowerChecker.endpoint_valid_sound`; the proof compares each rounded
  scale with the actual branch scale (`row_scale_rational`) and uses
  monotonicity of `rpow`, as before. The binary power literal is the
  unreduced `1549247890379023302829202/10^25`, which `rfl` identifies with
  `componentPowers 8`.
- **Weakened constant.** The binary initialization constant remains `1/4`,
  below the certificate's `0.3551`; `rational_seed_bound` checks it for all 25
  states, and the depth margin is still at least 45.

### Lean v4.35.0-rc2 and the module system (2026-10-06)

The same source was then moved to Lean v4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, as Palomar now requires. Every
file starts with `module`, imports with `public import` and wraps its
declarations in `@[expose] public section`, with
`backward.privateInPublic` so that the generated `private` certificate chunks
remain usable from public proofs. These headers change visibility only: no
statement, definition or certificate value changed, and Challenge and
Solution differ from their previous text only in the header lines. Three
proofs were repaired for the new versions: `Finset.prod_le_prod₀` replaces a
renamed Mathlib lemma; `component_base` now rewrites with the equation lemma
instead of letting the kernel evaluate `4^(10^20)`; and the prime-chain
ordering is checked by a Boolean function `primeChainCheck` with a proved
soundness lemma `primeChainOrdered_of_check`, replacing a `decide` that no
longer reduces through `ZMod`. The soundness lemma quantifies over every
`z : ZMod p`, exactly as `PrimeChainOrdered` does. The (19,23) order table is
reformatted to at most 100 characters per line, which keeps every file below
Palomar's 10,000-line limit.

The build, axiom audit, `leanchecker` kernel replays and the bundled
comparator run (Lean's kernel, NanoDa and con-ron) of this source are recorded
in [verification/README.md](verification/README.md).
