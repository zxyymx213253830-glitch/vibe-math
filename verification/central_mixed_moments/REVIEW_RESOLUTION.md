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


## General central rectangle: actual factorial formula and P4 objections

The next real Qoder review covers full polynomial source transport files and
reports no concrete mathematical issue. Its finite-sum comment should be
read WITH the integrability premises actually discharged in the source;
Bochner integration is not unconditionally additive on arbitrary functions.

The general-minimum P4 then raises two incorrect high-severity objections:
1. M positivity is NOT deduced from K or a density. M is DEFINED as the finite
product of positive factorial ratios and positivity proved directly with
Finset.prod_pos / positivity. K0=M*Kd is a separate factorial identity.
There is no circularity or missing invertibility; M>0 implies M!=0.
2. No rectangular determinant EXPECTATION is equated to a square one with
a constant RN derivative. The review invents such an equation. The actual
proved statement is a TAIL probability after cone translation:
 Pr_rect(W>xI)=Kd exp(-nx) int_{V>0} det(V+xI)^d exp(-tr V) dV.
The SQUARE Wishart DENSITY is K0 exp(-tr V), on the SAME n-by-n Hermitian
cone; hence its expectation equals K0 times exactly that last integral.
Dividing by K0 gives Pr_rect=exp(-nx)*(Kd/K0)*E_square[det(W+xI)^d].
Both rectangular and square Gram matrices have n-by-n dimensions; their
sample matrices have different row counts, not the target Hermitian space.
No square submatrix projection of a rectangular sample is used or needed.
The ratio Kd/K0=1/M and the square expectation's explicit factorial
functional are independently proved, completing the formula.

The review correctly resolves its own conjugate-order, real-power and
Bochner objections. Tail complement requires only total mass1 and Borel
measurability, not a missing atom-free assumption: {min<=x} is exactly the
complement of {x<min}. Full all-real CDF follows min>=0 pointwise.
These responses clarify the actual proof, not modifications to placate
false claims. [需人工审查] human model/measure correspondence still required.


## Arbitrary-mean moments and specializations

Qoder supplied an actual direct P4 response with no concrete blocking issue
in full noncentral source and the supplied specialization script. Noncentral
source hash is the checked final file. Specialization d0 proof still needed
explicit rw[0+n=n] in the hidden Gaussian source type AFTER that review;
final specialize-4 passes, same theorem, but final tactic change is outside
its exact reviewed snapshot. This is reported rather than rewriting history.
The d1/d2 specializations and all noncentral statements were unchanged.
Noncentral fixedseed2026101906 actual200000 sample controls use known ncx2
trace moments1,2,3 and shifted Gram determinant powers1,2,3; all pass, not
proof. No noncentral minimum CDF or closed spectral density is inferred.


Final Qoder P4 delivered on exact checked linear/univariate sources: no concrete defect reported; linearity vs multiplicativity, coefficient evaluation commutation and Gram polynomial confirmed within supplied scope. Human measure/model interpretation still required, no independent compile. Raw response and source hashes preserved.


## Resumed degree and normalization checkpoint

Prior quota-closeout is preserved as a historical snapshot; the user renewed
authorization after it, with a new ordinary-allowed quota window. No reset or
purchase was requested/used. New exact polynomial/factorial controls precede
proofs. Degree-1 hit deterministic Lean heartbeats in matrix-one type
unification, not a failed mathematical conjecture; degree-4 uses explicit
entrywise identity and passes under the same default heartbeat limit.

Qoder degree P4 reports no blocking issue on exact final9-statement source.
Its n0 explanation saying P=(X+1)^d is incorrect: the matrix is empty, its
determinant is1, so P=1. Code and degree0 conclusion are correct. L(1)=1
is proved directly by simp on the explicit factorial coefficient functional,
not an assumed normalization axiom. The independent constant-term bridge
uses the actual Gamma determinant moment law, not the desired minimum CDF.
Normalization3 statements already kernel PASS; P4 response pending.

Normalization P4 delivered on exact final3 sources. Its warning about arbitrary ENNReal.toReal injection is inapplicable to the actual hi at that step: both sides are already ENNReal.ofReal of explicit real quantities, hence finite unconditionally, and toReal_ofReal only requires their proved nonnegativity. No extra finiteness or integrability premise is missing. The earlier norm-moment theorem takes row surplus d, dimension n, integer power p, with no invented m<=n hypothesis; d0 specialization is square.

Final real/right-tail P4 delivered on both exact checked files: coefficientwise real extraction, monicity, atTop filters, exp sign, covariance exponent v^(d*n) and CDF complement confirmed within source scope. No concrete mathematical issue reported. This is not independent compilation or human semantic review. Left-tail/T4 remains separate.


## General hard-edge route: actual obligations, not planning assertions

The real Qoder P1 favors residual/Gamma sandwich but incorrectly doubts the
deterministic lower bound minGram<=D_j. It holds for ALL matrices: a residual
test coefficient vector has u_j=1, norm>=1 and A*u equal to that residual;
Rayleigh min bound and minGram>=0 prove it. GramMinimumResidualLower now
checks this exactly, with no rank/generic-position premise. The planning
response also treats the actual per-column Gamma law as already instantiated;
only the underlying fresh-column/random-projection framework is proved so
far. Leave-one-out marginal transport and final event sandwich remain to do.
Finally a single determinant mass M does NOT determine Q low derivatives;
the full Gaussian polynomial functional is needed for analytic cancellations.
No exact general T4 coefficient follows merely from the loose Gamma bounds.

Residual P4 supplied hypothetical conjugate-linearity/refactor warnings, not a current defect: Submodule.starProjection has type ContinuousLinearMap over complex scalars. complexGram is explicitly A.conjTranspose*A. smallestEigenvalueIndex selects Fin.last of the DESCENDING eigenvalue list, not an ascending first index; the review condition asking for ascending indexing is mistaken. The checked Rayleigh/smallest-tail equivalence fixes the exact minimum. Nonnegativity is the previously proved PSD Gram eigenvalue lemma with no rank premise. Review shorthand saying D_j<=n*lambda for everyj is not the theorem; only EXISTS a suitablej.


Gaussian residual P4 delivered on exact complex/real projection8 statements.
The total inverse is the ordinary nonsingular inverse with zero on the ENTIRE
singular branch, not a Moore-Penrose pseudoinverse. The global real subspace
was intentionally defined bottom on that branch, so equality with the total
zero projector is global; actual column-space agreement is gated by explicit
fullrank. Imported actualColumnAppend_split_energy_law is unconditional and
uses proved actual Gaussian fullrank, not a conditional law. Orthogonal
complex/real complement equality here is of PROJECTIONS, derived from the
two direct-sum decompositions and equality of projected vectors; no unsupported
subspace equality or hidden rank choice is invoked. Actual per-column Gamma
law now proved by fixed permutation, and event inclusion uses AE fullrank
for deleted submatrices. Different residuals are never called independent.


Final Gamma sandwich P4 delivered13 exact-source statements. Its alleged
ae_map_iff bimeasurability gap is false: locked MeasureTheory.ae_map_iff
requires AEMeasurable f and MeasurableSet predicate, both explicit in code.
No inverse-measurability premise exists. Deterministic lower/upper residual
inequalities were proved for ALL matrices, so no missing full-matrix rank
assumption is needed. Full rank of the deleted Gaussian block is proved AE
using the actual injected-column Gaussian marginal; IsUnit det over C is
equivalent to nonzero and is the exact inverse-projector prerequisite.
Rate1 is inherited from actual CN divide-sqrt2 source, not an unverified
new convention. The CDF identity uses cdf_eq_real for a probability measure
on ALL reals, so negative thresholds require no additional branch argument.
Boundary r1 is explicitly excluded in this r>=2 theorem; existing scalar
Gamma law covers it separately. All mathematical warnings are documented,
not silently converted into a blanket review approval.


## Hard-edge bounds P4 (exact final six-declaration source)
Real Qoder response preserved. Its high type claim is false: locked Mathlib MeasureSpaceDef.lean defines `Measure.real mu s := (mu s).toReal`, not a measure on R. `stdGaussian` has `isProbabilityMeasure_stdGaussian`; event measurability follows `measurable_centralGaussianSampleMinimum` and Iic, with actual pushforward handled in prior checked marginal sources. The N prefactor is exactly `measureReal_iUnion_fintype_le`, independent of residual independence. The N inside threshold is from deterministic exists j D_j<=N*lambda, not variance. Both are necessary and a checked stated sandwich supplies them. No claim that local constant exp(-1)/factorial works globally: local theorem requires0<x<=1 and Theta uses nhdsGT0. d=0 is included, N=1 excluded here, sharp coefficient not claimed. Imported dependency questions were previously reviewed; this response is not an independent compile or human approval.
