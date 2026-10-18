# Real collaboration, corrections, and remaining review

Proof bodies: Codex. Qoder provided bounded P1/P4 feedback, not proof bodies.
All original requests, raw responses, stderr, receipts and failed Lean logs kept.
[需人工审查] Weighted measures, product integration, actual variance/source-paper
correspondence. Model delivery is not independent compilation or human approval.

## P1 structural discussion

The overlapping-minor formula passed 3 shapes x200000 actual CN samples with
Gamma trace/full determinant controls, plus higher powers and weighted trace
controls. Numbers are NOT proof. Qoder endorsed the shared-column route but
incorrectly said the two selected determinants are not conditionally independent
given the common columns; once those are fixed their common determinant is
constant and the exclusive Gaussian blocks are conditionally independent.
The projected residual actual Wishart law also does not follow from ordinary
column selection alone; that is an additional rotational/skew-product result.
Our formal route instead uses the ALREADY PROVED whole Bartlett block joint law.

## Qoder size-bias review: preserve and reject false alarms

* n=0: the empty product is1 and 0<1 is true. Degenerate zero-dimensional law
  causes no contradiction and is handled in the existing actual density theorem.
* d=0 square Gaussian Gram is positive definite almost surely, not singular.
  Existing actual Gaussian full-rank theorem and density proof settle this.
* Increasing and decreasing orders of the SAME finite factorial factors have
  the same product; the review's termwise comparison ignored permutation.
* A principal k-column selection of an actual t-row Gram has t rows. It is NOT
  a Schur complement, whose residual row count can decrease. Both source law
  and `complexWishart_principalSubmatrix_law` state the unchanged t explicitly.
  The suggested t-n+k rule was false for this principal marginal.

The exact actual density and its normalization are imported checked assets,
not postulated by this new module. The weighted measure is UNNORMALIZED with
mass centralDeterminantPowerMoment; no accidental probability instance added.

## Qoder shared-pivot review: squared-norm versus norm confusion

The pivot r is the squared complex-column norm and has Gamma(m+1,rate1), not a
raw norm. The exact chart is [[r,sqrt(r)z],[sqrt(r)z^H,B+z^H z]]. Therefore its
determinant is r det(B), as the checked imported Schur factor proves. Scalar
control r=4,z=1,B=3 gives [[4,2],[2,4]], det12=rB, not r²B. The suggested
missing conjugation/square and half-integer Gamma exponent are false alarms.
The final proof explicitly guards r>0 almost surely and uses real Gamma power
p+q. Pushforward integration requires measurability, not a measurable equivalence;
`complexWishart_centralBartlett_recursion` supplies the actual pushforward.

## Claude attempt

A real bounded Claude Code P4 supplied the complete bias and principal-selection
sources. It timed out at120s with no successful final response (exit124).
It does not count as delivered review; no retries or manufactured conclusion.

## Precise current boundary

The common-prefix theorem is dimension-general, but arbitrary Finset overlap
still needs canonical reindexing. A d>1 minimum integral is NOT proved merely
by these two-minor moments. No general spectral G2/T1-4 or T3 source decision.


## Full joint-source P4 with exact chart context

The last real Qoder review supplies all three final disjoint/pivot/prefix sources
and the exact imported chart definition. It correctly recognizes squared-norm
pivot, unchanged principal row count, product order equivalence, empty products
and overlap dependence. Remaining queries concern API generality, not a stated
mathematical counterexample: `stdGaussian_map_injective_coordinates` quantifies
arbitrary finite index TYPES (including Sum); `centralBartlettGram_det {n : Nat}`
is dimension-polymorphic; Nat addition on the right handles k+0 and successors;
`fun_prop` constructs measurable proofs checked by the kernel. All exact calls
are in the final exit0 logs, not suppressed missing assumptions. We do not
claim imported measure/model interpretation was independently checked here.


## New finite-pair and two-extra-row review calls

The real 3-source finite-Venn/mixed request timed out after120s (exit124), no
successful final response. It is not counted as a delivered review. Exact
kernel evidence nonetheless separately checks all sources and the constructed
finiteMinorOverlapModel, whose printed axioms are standard. No sorry remains.

The real 3-source second-moment/spectral-bridge/two-extra-row review completed.
It reports no local mathematical counterexample; its remaining scale question
is answered by `complexSampleMatrix` dividing real source pairs by sqrt(2).
Actual trace law Gamma(m*n,rate1) is independently formally proved and the
numeric controls match this convention, not total variance2. Deterministic
minimum scaling by a^2 does NOT depend on the base variance; the review's
hypothetical a^2/2 alternative is false. Paper convention still requires humans.

Its explanation about multiplying two extra-row pivots is not used: the proven
normalizing ratio is K(2,n)/K(0,n)=1/(n!(n+1)!), obtained from factorial products;
the averaged squared determinant belongs to the ACTUAL SQUARE n-by-n law.
The reference integral retains exp(-tr V) through centralConeWeight 0; the
review's shortened displayed equation dropping that factor is not the code.
Strict-tail/weak-CDF are exact complements; no boundary-nullity premise added.
No general original T1 or G2 equality is inferred from this new polynomial.


## Grouping review and natural-subtraction false alarm

The real grouped-source P4 verifies the multiplicity formula but asserts that
`centralMixedMinorMoment_eq_byCards` needs t>=S.card/T.card because omega is
"unsound" with truncated subtraction. This is false. For ALL naturals,
(t-c)-a=t-(c+a); finiteMinorOverlap_left_card gives c+a=S.card. This holds
also for t<S.card, e.g. t=0,c=a=1 yields0=0. The theorem only equates two
explicit coefficient FUNCTIONS there, not a wide-Wishart actual moment.
The actual moment theorem separately requires n<=t. No guard is missing.
The remaining embedding/simp/rewrite warnings are proof-engine API speculation
already answered by final exit0 checks. No source change or extra assumption
was made merely to placate those false alarms; human model review remains.


## Actual scalar CN and finite polynomial moments

New scalar P4 delivered concrete source scope; its sole API concern asks
whether integral_map needs Integrable instead of AEMeasurable. Locked mathlib
integral_map uses the exact measurability obligations discharged in phase-2
exit0. Full monomial integrability is separately proved in monomial-4.
No hypothetical missing-integrability premise was introduced. New polynomial
P4 did NOT deliver an issues-only review: it emitted a fake tool-call fragment
with tools disabled. It is preserved verbatim, not treated as review approval.

Earlier complex-p1 suggested a ring homomorphism into L2/integrable functions
and closure of integrable products. Those are false in general. The code
uses only a polynomial evaluation ring map into ordinary functions; integrals
are linear. Independent coordinate products are integrable by the exact
mathlib Integrable.fintype_prod theorem, not by general L1 product closure.
Fixedseed2026101905 controls evaluate finite polynomials with factorial
contraction, a known CN(0,2) fourth moment8 and Exp1/Gamma trace controls.
A new5x2 d3 minimum numerical comparison is empirical, NOT a Lean d3 theorem.
All new proof bodies Codex. [需人工审查] Fubini/model/variance remain.
