# From finite interval certificates to the exponent

This is an informal account of the argument proved in the Lean project.
It replaces the entropy and composition-rounding passage in the research
notes with finite stopping words. The project also proves the prime-chain,
odd free-digit, and binary recursive constructions that supply the finite
alphabets. All six prime chains, the full binary component, and both complete
odd witnesses are proved, including their numerical moments. Their concrete
certificates establish the full exponent 0.75806746 without additional
mathematical hypotheses.

## Finite input and conclusion

For a nonempty finite index set, let \(b_i>1\) be pairwise coprime perfect
squares. Choose finite canonical digit sets \(C_i\) modulo \(b_i\). Associate
to each digit \(x\) an interval
\[
[a_{i,x},a_{i,x}+w_{i,x}]\subseteq[0,1],
\qquad 0<\sigma\le w_{i,x}\le\rho<1.
\]
Whenever distinct digits satisfy \(y-x\equiv z^2\pmod{b_i}\), require
\(a_{i,x}+w_{i,x}\le a_{i,y}\). Incomparable digits may have overlapping
intervals.

Let \(\alpha\ge0\) and \(f_i\ge0\). Assume the finite moment inequalities
\[
Z_i:=\sum_{x\in C_i}w_{i,x}^{f_i}\ge b_i^\alpha,
\qquad F:=\sum_i f_i>\alpha.
\]
Then, for every \(\varepsilon>0\) and all sufficiently large natural \(N\),
there exists a square-difference-free \(A\subseteq[1,N]\) with
\[
|A|\ge N^{\alpha-\varepsilon}.
\]
This is `interval_moment_exponent` in [Moment.lean](Sarkozy/Moment.lean).
No word-selection or asymptotic assertion is a hypothesis of that theorem.
For a fixed finite family, the common bounds \(\sigma,\rho\) follow from
pointwise \(0<w_{i,x}<1\); Section 9 explains this additional proved step.

## 1. Words preserve interval ordering

Encode a length-\(k\) word by \(\sum_{j<k}x_jb^j\) and attach its nested
affine interval using \(t\mapsto a_x+w_xt\), reading the low digit first.
Its width is \(W=\prod_jw_{x_j}\).

If two low digits differ, a modular square difference orders their
intervals, hence all nested subintervals. If the low digits agree and
\(b=s^2\), divisibility \(s^2\mid z^2\) implies \(s\mid z\).
Dividing the difference by \(b\) therefore leaves a modular square
difference between the tails. Induction proves interval ordering for all
words. Canonical encoding is injective.
These steps are in [Words.lean](Sarkozy/Words.lean) and
[Intervals.lean](Sarkozy/Intervals.lean).

## 2. Stop when the width reaches a common threshold

Fix a positive integer \(K\) and put \(\delta=\rho^K\), so \(0<\delta<1\).
Begin with the empty word, whose width is one. Extend each active word
by every digit. Keep a child active when its width exceeds \(\delta\);
otherwise mark it terminal.

All words terminate by depth \(K\), since a depth-\(K\) width is at most
\(\rho^K=\delta\). Every terminal word has width at most \(\delta\)
and strictly greater than \(\delta\sigma\): its parent was wider than
\(\delta\), and the last digit has width at least \(\sigma\).

For one component, write \(q=b^\alpha>0\), \(f=f_i\), and \(Z=Z_i\ge q\).
Let \(A_j\) be the sum of \(W^f\) over active depth-\(j\) words, and \(T_j\)
the sum over terminal depth-\(j+1\) words. Exact multiplicativity gives
\[
A_0=1,\qquad A_K=0,\qquad A_{j+1}+T_j=ZA_j.
\]
Consequently some \(j<K\) satisfies
\[
q^{j+1}\le (K+1)T_j.
\]
Otherwise induction would give
\(A_j\ge q^j(K+1-j)/(K+1)\), contradicting \(A_K=0\).

Keep those terminal words of the one length \(k=j+1\), calling their
encoded set \(D\). Each terminal width is at most \(\delta\), so
\(T_j\le |D|\delta^f\). Thus
\[
1\le k\le K,\qquad
(b^k)^\alpha\le |D|\delta^f(K+1).
\]
Every selected interval still has width at least \(\delta\sigma\).
The complete finite argument is `stopping_selection` in
[Stopping.lean](Sarkozy/Stopping.lean).

## 3. Round intervals to ranks and combine components

For a selected interval with left endpoint \(A_x\), use
\[
r(x)=\left\lfloor\frac{A_x}{\delta\sigma}\right\rfloor,
\qquad H=\left\lceil\frac1{\delta\sigma}\right\rceil.
\]
Ordered intervals are separated by at least \(\delta\sigma\), so modular
square differences strictly increase the rank. The ranks satisfy
\(0\le r(x)<H\).

Apply the selection independently in each component. Let \(n\) be the
number of components, \(M=\prod_i b_i^{k_i}\), and \(Q=\prod_i|D_i|\).
CRT produces \(Q\) canonical residues modulo the square \(M\).
Summing the component ranks gives ranks below
\(h=1+n(H-1)\), and the cardinality inequalities multiply to
\[
M^\alpha\le Q\delta^F(K+1)^n.
\]
For the fixed positive constant \(c=(n+1)(1+\sigma^{-1})\),
the ceiling bound gives \(h\le c/\delta\).

## 4. A strict contribution surplus gives one finite block

Because \(F>\alpha\), the quantity
\(\delta^{\alpha-F}=(\rho^{\alpha-F})^K\) grows exponentially in \(K\).
It eventually dominates the fixed polynomial \(c^\alpha(K+1)^n\).
For such a \(K\), the preceding estimates give
\[
(Mh)^\alpha
 \le M^\alpha c^\alpha\delta^{-\alpha}
 \le Q\,c^\alpha(K+1)^n\delta^{F-\alpha}
 \le Q.
\]
This yields one finite ranked alphabet with base \(M\), rank height \(h\),
and cardinality at least \((Mh)^\alpha\). The growth and rounding
estimates are proved in [Growth.lean](Sarkozy/Growth.lean).

## 5. Amplify the finite block and cover every large N

Repeat the resulting alphabet in square base \(M\). The integer rank of a
word is the lexicographic rank word, with low numerical digits read first.
The word proof gives \(Q^t\) ranked residues modulo \(M^t\), with ranks
below \(h^t\). Reverse-rank representatives give \(Q^t\) square-difference-free
integers in \([1,(Mh)^t]\).

Put \(L=Mh>1\). For any positive \(N\), choose \(t=\lfloor\log_LN\rfloor\).
Then \(L^t\le N<L^{t+1}\), and
\[
N^\alpha\le Q^{t+1}=Q\,|A|.
\]
For any \(\varepsilon>0\), eventually \(N^\varepsilon\ge Q\), so
\(|A|\ge N^{\alpha-\varepsilon}\). This passage is
[Asymptotic.lean](Sarkozy/Asymptotic.lean); the reusable finite criterion is
[Certificate.lean](Sarkozy/Certificate.lean).

## 6. Prime-chain alphabets and their numerical moments

[PrimeChains.lean](Sarkozy/PrimeChains.lean) constructs the six chains at
\(p=3,7,11,31,59,103\), with respective lengths \(t=2,3,4,7,9,11\).
The entries are the exact arrays displayed in the paper. For a chain
\(s_0,\ldots,s_{t-1}\), the alphabet is
\[
C=\{s_j+pu:0\le j<t,\ 0\le u<p\}\subseteq[0,p^2).
\]
Every copy of \(s_j\) receives the interval \([j/t,(j+1)/t]\).
Canonical bounds and injectivity give exactly \(pt\) digits.

If a square edge preserves the low digit, then \(p\mid z^2\), so primality
gives \(p\mid z\). Consequently \(p^2\mid y-x\), forcing \(x=y\) by
canonical bounds. For different low digits, a finite check proves that a
square edge modulo \(p\) points from the earlier to the later chain index.
These checks, and distinctness of the chain entries, use ordinary kernel
`decide`. They establish interval ordering modulo \(p^2\). The exact moment is
\[
Z_f=pt\left(\frac1t\right)^f=pt^{1-f}.
\]
The widths of these six alphabets lie between \(1/11\) and \(1/2\).

[ChainMoments.lean](Sarkozy/ChainMoments.lean) proves the six numerical
moment inequalities for the exact exponent and rational powers in
[Parameters.lean](Sarkozy/Parameters.lean). It suffices to prove
\[
(2\alpha-1)\log p\le(1-f)\log t.
\]
The logarithmic bounds have short arithmetic certificates. Fix
\(D=10^{35}\) and \(n=52\). For a positive integer \(x\), choose positive
integer lower and upper ladders starting at \(L_0=U_0=xD\), with
\[
L_{k+1}^2\le DL_k,\qquad DU_k\le U_{k+1}^2.
\]
Monotonicity of the logarithm and \(\log(y^2)=2\log y\) propagate these
relations through the ladder. Applying the proved elementary inequalities
\(1-y^{-1}\le\log y\le y-1\) at the last entries gives
\[
2^n\left(1-\frac D{L_n}\right)
 \le\log x\le
2^n\left(\frac{U_n}D-1\right).
\]
The generator
[generate-chain-log-bounds.py](scripts/generate-chain-log-bounds.py)
uses exact integer square roots to propose the ladders. Lean checks all
624 square comparisons for the twelve enclosures, their positivity and
endpoints, and the final rational inequalities. The generator is not a
trusted proof step; neither floating-point evaluation nor `native_decide`
is used. The resulting theorem `concretePrime_certified_moment` proves all
six actual alphabet moments without external hypotheses.

## 7. Odd free digits and CRT

[OddLift.lean](Sarkozy/OddLift.lean) proves the construction for any finite
support of correlated low points. At prime \(p\), a low word and a free
word are canonical base-\(p\) integers with \(e_p\) digits. Interleave them as
\[
x_p=\sum_{j<e_p}\bigl(a_{p,j}p^{2j}+u_{p,j}p^{2j+1}\bigr),
\qquad 0\le x_p<p^{2e_p}.
\]
The recursive definition reads the least significant digit first.

Suppose the difference of two interleaved words is a square modulo
\(p^{2e_p}\). If their first low digits agree, primality forces the square
root to be divisible by \(p\). Reduction modulo \(p^2\) then forces their
first free digits to agree as well. Cancelling these digits and dividing
by \(p^2\) leaves a square congruence for the remaining words. If instead
the first low digits differ, their nonzero difference is a square modulo
\(p\). Induction therefore gives the precise relation `PrimeLowRelated`:
the low words are identical, or their first differing digit has a square
difference in the required direction. The same induction proves that two
free copies of the same complete low word cannot form a nonzero square
edge.

Apply this argument separately at every prime coordinate. The position
of the first difference may vary with the prime. CRT and injectivity of
the interleaving give distinct canonical residues modulo
\[
F^2,\qquad F=\prod_p p^{e_p}.
\]
A nonzero square edge between lifted residues must have distinct low
points and must satisfy the low-word relation at every prime. Thus an
interval order verified on the low support orders all its free copies.
The theorem `odd_prime_interval_lift` proves the exact cardinality and
moment formulas
\[
|C|=F|S|,\qquad Z_f(C)=F\sum_{a\in S}w_a^f.
\]
It allows arbitrary correlations between low coordinates; the support is
not assumed to be a Cartesian product.

[OddTarget.lean](Sarkozy/OddTarget.lean) specializes this theorem to
three low digits at each of \((5,43)\) and \((19,23)\). This proves the
free multiplicities \(215^3,437^3\), the square bases \(215^6,437^6\), and
the lifted geometry and moments from the corresponding low certificates.
At this generic interface, the low supports, geometry, low-edge order and
moments are inputs. The concrete witnesses in Section 10 discharge them.

## 8. Binary policy recursion and exact moment growth

[Binary.lean](Sarkozy/Binary.lean),
[BinaryGrowth.lean](Sarkozy/BinaryGrowth.lean), and
[BinaryPolicy.lean](Sarkozy/BinaryPolicy.lean) prove that a finite valid
parity-window policy constructs ordered alphabets at every positive depth.
Each state has designated parity windows and at most four branches. A
branch selects a child state, translates or reflects its residue set,
places its intervals by a positive affine scale, and forms digits
\(r+4y\), with \(r\in\{0,1,2,3\}\).

Same-branch square differences cancel a factor of four and reduce to the
child ordering. Distinct branches differing by two modulo four cannot
form a square edge. Every remaining cross-branch square edge is odd, and
an odd square is one modulo eight. It therefore goes from numerical class
\(k\) to class \(k+1\pmod8\). The policy's containment and cyclic ordering
conditions on those eight class windows imply the required parent
ordering, including the wrap from class seven to class zero. Residue
reflection reverses the relevant child edge and is paired with interval
reflection; the parity calculation includes the branch translation.

The initial alphabet at depth one is a singleton occupying a designated
present parity window. The recursive `family` constructs the actual
finite sets and proves their canonical bounds and interval ordering in
base \(4^m\). No assertion about an expanded alphabet at depth \(m\) is
assumed. Injective residue transformations and disjoint base-four branches
also prove the exact recurrence
\[
Z_{s,m+1}=\sum_{r\in R_s}u_{s,r}^{f_B}
                 Z_{\operatorname{child}(s,r),m}.
\]
If a comparison vector satisfies
\[
c v_s\le d_s,\qquad
 a v_s\le\sum_{r\in R_s}u_{s,r}^{f_B}v_{\operatorname{child}(s,r)},
\]
where \(d_s\) is the seed-window width and \(f_B\le1\), then
\(d_s^{f_B}\ge d_s\). Induction on this exact recurrence gives
\(Z_{s,m}\ge c a^{m-1}v_s\). This step does not assume a spectral limit.

At the root, \(v_{\rm root}=1\). Halving every final interval width while
keeping its left endpoint preserves ordering and gives widths at most
\(1/2\). The moment is multiplied by exactly \(2^{-f_B}\). Thus the single
finite depth comparison
\[
\alpha m\log4\le\log c+(m-1)\log a-f_B\log2
\]
implies the required root moment \(Z\ge(4^m)^\alpha\).

[BinaryRealData.lean](Sarkozy/BinaryRealData.lean) supplies the exact
25-state rational policy and proves its real policy validity.
[RecordBinaryTarget.lean](Sarkozy/RecordBinaryTarget.lean) fixes its
comparison vector, root, \(m=10^{10}\), and
\[
a=\frac{1430118728343}{500000000000},\qquad c=\frac14.
\]
The simpler initialization constant \(1/4\) is smaller than the constant
in the paper; its seed inequalities are checked in Lean. This module
constructs the binary interval certificate from only `RecordBinary.Rows`
(the 25 real-power row inequalities) and `RecordBinary.DepthCondition`
(the displayed depth comparison with this choice of \(c\)).

[BinaryDepth.lean](Sarkozy/BinaryDepth.lean) fully discharges the depth
condition. Two more 52-step integer ladders, with the same denominator
\(10^{35}\), certify
\[
1.050904648198512\le\log a,\qquad
\log2\le0.693147180559946.
\]
All 104 additional square comparisons are kernel checked. The lower
ladder starts at the exact rational growth parameter, encoded with this
common denominator. Rewriting \(\log4=2\log2\) and
\(\log(1/4)=-2\log2\) reduces the depth check to rational arithmetic.
The proved theorem `RecordBinary.depth_margin` gives
\[
\log(1/4)+(m-1)\log a-f_B\log2-\alpha m\log4\ge27.
\]
Thus `RecordBinary.depth_condition` has no hypotheses.

[BinaryRows.lean](Sarkozy/BinaryRows.lean) also discharges all 25 row
inequalities. The 94 branches use 54 distinct downward-rounded rational
scales. For each rounded scale \(u\), it certifies a rational lower bound
\(L\le u^{f_B}\) using two square-root ladders. A lower ladder bounds
\(\log u\) from below, and an upper ladder bounds \(\log L\) from above.
The terminal integer comparison proves
\[
\log L\le 2^{36}(b_{36}-1)
 \le f_B\,2^{36}(1-a_{36}^{-1})
 \le f_B\log u,
\]
where \(a_k,b_k\) denote the normalized positive ladder entries. Exponentiating
gives the required real-power bound. Each ladder has 36 steps and 37
entries, with common denominator \(10^{26}\): there are exactly
\(54\cdot2\cdot37=3996\) integer entries. Their square relations, positivity,
initial values, and terminal comparisons are all kernel checked.

Lean also verifies that every rounded scale is at most its actual branch
scale. Since \(f_B\ge0\), monotonicity transfers the lower power bound to
the actual branch. The positive comparison vector then allows 25 exact
rational weighted sums to establish `RecordBinary.rows_verified : Rows`
without hypotheses. The generator's proposed endpoints are not trusted
numerical approximations; their sufficient inequalities are proved in Lean.
Together with the depth theorem, this fully verifies the binary component.
The theorem `record_binary_interval_certificate` in
[TwoOddTarget.lean](Sarkozy/TwoOddTarget.lean) constructs its canonical
ordered alphabet and proves its target moment without external inputs.

## 9. Common width bounds follow from finiteness

[FiniteAlphabets.lean](Sarkozy/FiniteAlphabets.lean) proves that injectively
indexed digit constructions can be represented by finite sets without
changing their cardinalities or moments. Interval functions are extended
to all integers, but every required property is restricted to the actual
digit set.

For the resulting finite family, collect all widths and adjoin \(1/2\).
This gives a nonempty finite set whose elements lie strictly between zero
and one. Its minimum \(\sigma\) and maximum \(\rho\) satisfy
\[
0<\sigma\le w_{i,x}\le\rho<1.
\]
Consequently `interval_moment_exponent_of_pointwise_widths` requires only
pointwise finite geometry, ordering, and moments. Researchers need not
supply common constants or compute a minimum across an enormous expanded
binary alphabet. The final halving in Section 8 ensures the binary widths
satisfy the strict upper bound needed here.

## 10. Exact finite witnesses and compact numerical checks

[OddData437.lean](Sarkozy/OddData437.lean) encodes all 19,683 rows of the
reconstructed depth-three witness at primes 19 and 23. As for the 4,913-row
215 witness, each row contains two packed low words, an integer interval
start, and an integer width. Lean checks canonical coordinates, positive
widths below the common denominator, and containment in the unit interval.
Strictly increasing packed-coordinate keys prove that the points are distinct.
These data checks establish the actual geometry. The edge-order and moment
proofs below then complete both odd certificates.

[OddOrder.lean](Sarkozy/OddOrder.lean) and
[OddOrderCertificate.lean](Sarkozy/OddOrderCertificate.lean) prove a compressed
edge-order checker. Index rows by increasing right endpoint. For each prime
and each low-digit prefix, store a natural-number bit mask containing all
source rows with that prefix. Containment suffices; exact equality of these
masks with their intended sets is unnecessary. Each source's membership is
checked directly.

For a target low word, the first-difference relation determines a union of
prefix masks: equal digits recurse, and a different digit must differ by a
square modulo the prime. Intersect the two prime-specific masks. A proved
soundness lemma says that every relevant source appears in this intersection.
For each target, an integer cutoff records a prefix of the endpoint-sorted
rows whose right endpoints are at most its start. Check that the intersected
mask is contained in this prefix together with the target's own bit. Every
nontrivial square edge then has its source interval entirely before the
target interval. The checked endpoint lookup identities and prefix
containment make the auxiliary lookup trees untrusted certificate data;
no correctness assumption about their generation or internal shape is used.
The actual checks are split into consecutive blocks of at most 128 rows: 39
blocks for 215 and 154 blocks for 437. A proved block-coverage lemma combines their Boolean results into the
full source and target checks. Chunking limits evaluation memory and lets
builds preserve completed checks. A separate extensional lemma justifies the
numeric materialization used to speed up repeated prefix queries; it changes
neither the relation nor the certificate requirements. Large masks factor
trailing zero bits into exact natural-number shifts. The reconstructed masks
are checked by the same source and target predicates.

[OddMoments.lean](Sarkozy/OddMoments.lean) separates the moment calculation
from the geometric row order. Equality of sorted width lists proves equality of their multisets.
[OddKernelSort.lean](Sarkozy/OddKernelSort.lean) supplies a structurally
recursive implementation whose permutation property is proved for every
fuel value. Even insufficient fuel cannot certify a false multiset identity. Thus the indexed moment equals a sum over
distinct widths with their multiplicities. The transport is proved for any
real power, allowing the geometry and numerical certificates to use different
orders without changing the moment.

[PowerChecker.lean](Sarkozy/PowerChecker.lean) proves a reusable, exact
fractional-power checker. For rational \(0<x\le1\), put
\[
 P(x)=\sum_{i=1}^{8}\frac{(1-x)^i}{i},\qquad
 E(x)=\frac{(1-x)^9}{x}.
\]
A proved logarithm remainder bound gives
\[
 -P(x)-E(x)\le\log x\le-P(x)+E(x).
\]
The large odd moments use two terminal root bounds, without storing or
checking intermediate square-root ladders. Let \(D,A,B,L,H\) be positive
integers, with \(L,H\le D\), and put \(u=A/D\), \(v=B/D\), \(a=L/D\),
\(b=H/D\). For \(r=1024\), Lean checks
\[
 L^r\le AD^{r-1},\qquad BD^{r-1}\le H^r.
\]
After dividing by \(D^r\), these give \(a^r\le u\) and \(v\le b^r\), hence
\[
 r\log a\le\log u,\qquad \log v\le r\log b.
\]
For \(f\ge0\), the exact rational comparison
\[
 -P(b)+E(b)\le f\bigl(-P(a)-E(a)\bigr)
\]
therefore gives
\[
 \log v\le r\log b\le r(-P(b)+E(b))
 \le rf(-P(a)-E(a))\le f\log u.
\]
Exponentiating proves \(v\le u^f\). The generic Lean soundness theorem
works for every positive integer degree \(r=n+1\); the data instantiate
\(n=1023\). Positivity, both power inequalities, and the endpoint bounds
are part of the checked predicate. No square-root algorithm is trusted.

[PowerPolynomial.lean](Sarkozy/PowerPolynomial.lean) clears the positive
common denominator `840*X*D^8` for the input `X/D` in the eighth-order enclosure. It proves that
one natural-number polynomial comparison implies the rational logarithm
comparison above. This avoids repeated rational normalization in the large
finite checks without weakening their mathematical content.
[FastPowerCertificate.lean](Sarkozy/FastPowerCertificate.lean) packages the
integer tests and proves `PowerChecker.endpoint_valid_sound` once for both
odd witnesses. Their 20,769 distinct-width rows store their width,
multiplicity, proposed lower numerator, and two terminal root bounds.
The terminal bounds are unchanged from the earlier ten-step certificates;
the initial numerators are derived by exact scaling. The new proof checks
the terminal inequalities directly, so the eighteen intermediate entries
per row are no longer needed. The logarithm remainder estimate and the
passage to a real-power bound are proved in Lean; a generator's high-precision
proposal is never a trusted premise.

[Odd215Threshold.lean](Sarkozy/Odd215Threshold.lean) separately proves
\[
 (215^6)^\alpha\le215^3\,
 \frac{4088451159413731}{10^{12}}.
\]
Two 52-step integer square-root ladders prove
\(\log(4088451159413731/10^{12})\ge8.315921487685\) and
\(\log215\le5.370638028128\). With
\(\alpha=37903373/50000000\), the sufficient logarithmic comparison has
positive rational slack \(6.9459091072\cdot10^{-10}\). This scalar theorem
has no hypotheses. The actual 215 width sum is shown to be at least this lower sum by the
finite certificates described below.

## Specialization to the unconditional full exponent

[Parameters.lean](Sarkozy/Parameters.lean) fixes the six prime bases
\(3^2,7^2,11^2,31^2,59^2,103^2\), the odd bases \(215^6,437^6\), and the
binary base \(4^{10^{10}}\). Lean proves their coprimality and square-base
properties symbolically, without evaluating the huge binary power.
It also proves, with exact rational arithmetic,
\[
\alpha=\frac{37903373}{50000000}=0.75806746,\qquad
\sum_i f_i-\alpha=\frac{25671}{10^{12}}>0.
\]

The original theorem in [Target.lean](Sarkozy/Target.lean) takes nine
expanded interval alphabets. All nine components are now proved outright:
all six prime chains, both complete odd components, and the entire binary
component, including all their numerical moments. The odd lifts, common
finite width bounds, and the full asymptotic implication are also proved.

For 215, [Odd215MomentData.lean](Sarkozy/Odd215MomentData.lean) checks 1,861
distinct widths using 3,722 direct 1024th-power comparisons and 1,861 final
polynomial comparisons, together with positivity and scaling checks. The exact weighted lower sum is `4088451159413731/10^12`.
[Odd215Certificate.lean](Sarkozy/Odd215Certificate.lean) connects the histogram
to the endpoint-sorted geometry by a kernel-checked sorted-list identity.
It then combines every edge-order check with the threshold proved above,
and constructs the complete expanded 215 alphabet without assumptions.
[Odd215Moment.lean](Sarkozy/Odd215Moment.lean) also establishes the same moment
for the original packed-coordinate row order.

For 437, [Odd437MomentData.lean](Sarkozy/Odd437MomentData.lean) combines
18,908 distinct-width certificates with total multiplicity 19,683. The integer
width denominator is `10^16`, the power is `67871875356/10^12`, and the exact
weighted lower sum is `12261229628963862/10^12`. The endpoint certificates
require 37,816 direct 1024th-power comparisons and 18,908 polynomial comparisons.
The generated blocks each prove their histogram, weighted lower sum and
analytic moment bound; a generic addition lemma assembles the full result.
[Odd437Threshold.lean](Sarkozy/Odd437Threshold.lean) proves
`(437^6)^α ≤ 437^3 * (12261229628963862/10^12)` using 104 square comparisons.
Thus the actual width powers attain the required threshold.

[Odd437WidthHistogram.lean](Sarkozy/Odd437WidthHistogram.lean) proves that the
endpoint-sorted geometry has exactly this width histogram.
[Odd437Certificate.lean](Sarkozy/Odd437Certificate.lean) combines that identity
with the complete ordering and moment checks to construct the expanded 437 alphabet.
[Odd437Moment.lean](Sarkozy/Odd437Moment.lean) also verifies the moment for the
original packed-coordinate row order.

[FullTarget.lean](Sarkozy/FullTarget.lean) combines all nine complete components
in `Sarkozy.record_exponent`. The numerical submission statement
`SarkozySubmission.improved_bound` in [Solution.lean](Solution.lean) has no
certificate parameters or hypotheses: for every positive epsilon and all
sufficiently large N, it gives a square-difference-free subset of `[1,N]`
with cardinality at least `N^(37903373/50000000-epsilon)`.
No finite numerical, edge-order, lifting, counting or asymptotic assertion
remains an assumption. Earlier conditional interfaces and the illustrative
`exponent_three_fifths` theorem remain supporting library results.
