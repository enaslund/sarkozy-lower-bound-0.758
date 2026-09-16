# Semantic audit of the full lower bound

Reviewed 2026-09-11; numerical-checker extension reviewed 2026-09-14. **No mathematical or statement-level defect was found.**
The final theorem proves the intended square-difference-free lower bound with
the full exponent `0.75806746`. This is a source-level adversarial review;
fresh build and verifier results are recorded separately in
[verification/README.md](verification/README.md).

## What the theorem actually says

[`SarkozySubmission.improved_bound`](Solution.lean) has no hypotheses. Expanded
into ordinary mathematical notation, it states that for every real
\(\varepsilon>0\), there is a natural number \(N_0\) such that **every** natural
number \(N\geq N_0\) admits a finite set \(A\subseteq\mathbb Z\) satisfying

\[
 A\subseteq\{1,\ldots,N\},\qquad
 y-x\ne z^2\quad(x,y\in A,\ z\in\mathbb Z\setminus\{0\}),\qquad
 |A|\geq N^{37903373/50000000-\varepsilon}.
\]

This is the usual meaning of the lower bound
\(N^{0.75806746-o(1)}\). The quantifier order permits the set and the threshold
to depend on \(\varepsilon\), as required. It establishes all sufficiently
large \(N\), rather than merely an infinite subsequence.

The numeral `37903373 / 50000000` is division in **the real numbers**, exactly
`0.75806746`. The base `N` and cardinality are also cast to the reals in the
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
| Second odd component | \(437^6\), with primes 19 and 23 | `OddOrder437.interval_certificate` in [Odd437Certificate](Sarkozy/Odd437Certificate.lean) |
| Binary component | \(4^{10^{10}}\) | `RecordBinary.policy_valid`, `rows_verified`, `depth_condition`; assembled by `record_binary_interval_certificate` in [TwoOddTarget](Sarkozy/TwoOddTarget.lean) |

[Parameters](Sarkozy/Parameters.lean) proves that all nine bases are squares,
greater than one, and pairwise coprime. The nine moment powers are
nonnegative, and their sum exceeds the target exponent by exactly
`25671 / 1000000000000`. The strict surplus used to absorb losses is therefore
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
every depth. The depth `10^10` is an ordinary finite natural number; its
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

The endpoint cleanup preserves every width, multiplicity, lower numerator
and terminal root bound. Its new shared checker proves that two direct
integer power inequalities and the logarithm comparison imply the real-power
bound. The proof handles any positive integer degree and the certificates
use degree 1024. Its positivity hypotheses, denominator scalings and
inequality directions were checked; the general theorem separately passed
Lean and independent NanoDa. The integrated source also passed the complete Lean build, 76 axiom
inspections and full independent NanoDa replay; their exact coverage is in
[verification/README.md](verification/README.md).

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
