# Two-surplus central minimum: explicit sharp constant

2026-10-19. Proof bodies: Codex. Real bounded Qoder P1/P4 responses are archived;
Qoder supplied route criticism/review, not a proof body or independent compile.
[需人工审查] Inherited measure/Fubini, variance and actual-model interpretation.

Let X have N+2 rows and N columns, N>0, independent central complex Gaussian
entries with E|X_ij|^2=1. Let F(x)=Pr(lambda_min(X^H X)<=x). The checked result is

    F(x)/x^3 -> N*(N+1)*(N+2)/36   as x->0+.

The chosen analytic density core h satisfies

    h(x)/x^2 -> N*(N+1)*(N+2)/12.

This is not a claim about every representative of the AE-defined RN density.
N=n+1 in the actual-law Lean interface, so its sample is (n+3) by (n+1).
The N=1 case agrees with Gamma(shape3,rate1): F(x)~x^3/6. The formula is proved
for all N>0, not inferred from the finite parameter control.

The already proved actual CDF has form 1-exp(-N*x)*P(x)/M, where P is the raw
factorial-functional polynomial and M=mass(0,N,2)=N!*(N+1)!. No density premise
is added. Existing equality of the general actual law and the earlier
two-extra-row actual law identifies this normalized polynomial with

    Q(x)=SUM_(R,T subsets Fin N) x^(|R|+|T|) /
             ((|R union T|+1)*|R|!*|T|!).

The proof first simplifies the retained minor pair moment using bounds on
retained cardinalities, then explicitly reindexes BOTH finite sums by the
complement involution. The polynomial identity follows from equality of
evaluations on the infinite nonnegative real half-line. Its coefficients are
therefore coefficients of the independently identified actual-law polynomial.

Set r=|R|, h=|R intersect T| and t=|T minus R|. The multiplicity is
choose(N,r)*choose(r,h)*choose(N-r,t), the power is r+h+t, and the union size
is r+t. A generic binomial truncation lemma makes the low coefficient sums
bounded independently of N, with exact zero padding outside admissible sizes.
The checked coefficients are

    Q0=1, Q1=N, Q2=N^2/2,
    Q3=N*(N-1)*(5N+2)/36.

Small N=0,1,2 branches in the auxiliary binomial/cubic algebra are explicit;
the actual-law result itself requires N>0. The existing finite Taylor
convolution then gives N^3/6-Q3=N*(N+1)*(N+2)/36.

Asset audit: reused CentralWishartShiftedSecondMoment's exact moment cocycle
centralDeterminantPowerMoment_add and the existing factorial_ratio_product.
An initial duplicate declaration was rejected and removed, rather than counted
as a new asset. The new first-moment wrapper is a simple interface, not a new
probability theorem. Reused FiniteSubsetPairGrouping's exact pair reindexing.
No radial integral, joint spectral density, support theorem or numerical
experiment was reproved to obtain this result.

New files (19 printed declarations, of which two are actual-law asymptotic
corollaries): CentralWishartMomentFactorials (3),
CentralComplementMinorPolynomial (3), FiniteChooseTruncation (1),
CentralComplementLowCoefficients (2), CentralComplementCubic (5),
CentralTwoSurplusSharpCoefficient (5). Final leaf logs are moment-factorials-3,
complement-polynomial-2, choose-truncation-3, complement-low-1,
complement-cubic-2 and two-surplus-sharp-2. Actual main-entry check facade-26
exited0. All are serialized checks; the full Lake/mathlib build was NOT_RUN.
Failure logs retain duplicate-asset/API/normalization errors; no failed log
is represented as a successful check. All final printed axioms are the
standard propext, Classical.choice, Quot.sound only.

Exact-rational preflight used the previously committed independent grouped
polynomial control N1..12,d0..2. New factorial product control d,n0..12,p,q0..4
and fixed-seed2026101920 binomial truncation/control sumchoose=2^N also PASS.
They are controls, not proofs.

The real P1 response confused polynomial degree with missing union size,
reversed low/high powers and misstated N=1's degree. These claims were rejected;
the exact definitions above were supplied to P4. The final P4 response covers
the exact six source hashes, reports no concrete issue within this algebraic
scope and explicitly leaves inherited probabilistic interpretation to human
review. It is neither human approval nor independent compilation.

For general surplus d, the simplified candidate
(N+d)!/((N-1)!*((d+1)!)^2) is still NOT proved equal to the finite coefficient.
This d=2 result is consistent with that candidate but does not close the
general identity, original full T4 parameter mapping, noncentral sharp
coefficient, G2 or original general T1 determinant identity. Frozen manuscript,
PDF and submission/code archives remain unchanged.
