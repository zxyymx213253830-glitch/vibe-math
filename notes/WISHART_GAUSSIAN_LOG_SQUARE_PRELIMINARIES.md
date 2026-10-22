# Negative-log moments and one-variable square integrability — 2026-10-22

These eight new Codex declarations are PRELIMINARIES for the finite-dimensional polynomial log-square problem. The present accepted scope is a generic small-ball-to-moment theorem, uniform planar Gaussian root moments, and a one-variable polynomial negative-log square bound. This checkpoint does NOT yet claim a general multivariable/properCN1 log-square theorem, singular-model offset variance or logarithmic CLT.

For any probability measuremu, measurable real f, andC>=0 satisfying

    mu.real{f<=x} <= C x   for everyx>0,

the new theorem proves, for every naturalq,

    E[max(0,-Real.log f)^(q+1)] <= C (q+1)!,

with true integrability of that power. No sign hypothesis onf is needed: for negativef the upper-tail inclusion in{f<=exp(-t)} holds automatically. The input small-ball condition is strong, not a claim for arbitrary signed random variables. Real.log is totalized at0, withReal.log0=0; negative arguments use mathlib's real logarithm of the absolute value. No extended-real value minusinfinity occurs in these literal statements. Weighted layercake and the standard Gamma integral identify the factorial; these integration foundations are imported assets, not newly proved probability theory.

For planar stdGaussian(C), each real coordinate has variance1 and the complex second moment is2. The existing disk bound supplies C=1/2 forf=||z-a||^2 uniformly in EVERY fixed complex roota. Since max(0,-log||z-a||^2)=2complexNegativeLog(z-a), we obtain

    E[complexNegativeLog(z-a)^k] <= k!/(2*2^k),     k>=1 natural.

In particular the root negative-log SECOND moment is at most1/4. This is not a properCN1 constant; that law has a different normalization. Root locations may repeat, so multiplicities in a polynomial factorization remain intact.

For a fixed polynomialP in one complex variable, degreed, the new result is

    E[complexNegativeLog(P(z))^2]
       <= 2complexNegativeLog(leadingCoeff P)^2 + d^2/2.

It proves trueL1 of the square as well. The finite-root product bound is d^2/4, by subadditivity of the negative logarithm and the finite Cauchy–Schwarz inequality; splitting off the leading coefficient uses(a+b)^2<=2a^2+2b^2. The statement includes constants, empty root lists andP=0. In the zero case leading coefficient0, natDegree0, empty product1 and totalized negativeLog0=0 make the literal bound0<=0. No division by a leading coefficient is used and no roots are chosen measurably as parameters vary.

## Controls and verification

Fixed-seed2026102207 controls use200000 planar variance2 samples and28 tests. Products ofn0..3 independent coordinates are checked against Elognorm=(log2-EulerGamma)/2 andVarlognorm=pi^2/24. Shifted-root momentsk1..4 are compared with uniform bounds, and the centered root also has an independent one-dimensional quadrature check. Polynomial section degree/leading-coefficient bounds and normalization/totalized-zero/L1-versusL2 negative controls are recorded. They are reproducible implementation evidence, NOT a general proof.

The final source checks run through the existing single serial Windows gate. The three leaf modules contribute2+3+3 printed theorems. Independent literal expected types preserve all quantifiers, constants and absence of a sign/P!=0 hypothesis. A first type-checker attempt accidentally named its own proposition `Polynomial`, shadowing the polynomial type in that header; this failed exactly as intended. The failed checker copy, locks and logs are preserved asv1; corrected v2 names the propositionPolynomialSquare. It changes no proof-source bytes or theorem target. The prior v1 DAG records are explicitly superseded, not accepted. Final expected-type checking must pass before acceptance. Only the standard three axioms are accepted; no source bytes changed after the final P4 snapshots.

## Qoder collaboration and review dispositions

The real P1 route review recommended root factorization, uniform section bounds and leading-coefficient induction. Its proposed need for double induction on(n,degree) is false: the planned induction hypothesis atn quantifies EVERY polynomial in those n variables, regardless of degree. The leading coefficient lives in n variables, so induction on the number of variables suffices. Its scale concern is already accounted for by the explicit leading-coefficient negative-log term. The future section theorem will require joint evaluation measurability, coefficient-squareL1 and a FIXED deterministic degree bound, without a measurable choice of roots. That section theorem is outside this checkpoint.

The real final-source Qoder Qwen3.8-Max P4 returned in29.76seconds with tools/MCP disabled and zero retries, and no independent compilation. Full exact source/request/prompt/raw/receipt hashes are preserved. Its warnings and author dispositions are:

1. Alleged missing nonnegativef premise: false. The existing tail inclusion proof separately handlesf>0 andf<=0; in the latter branchf<=exp(-t) automatically. The reviewer also incorrectly says Real.log of negative numbers is0; the proof relies on neither that false convention nor positivity of signedf. The nonnegative random variable used for layercake isY=max(0,-Real.logf), whose nonnegativity is explicit by construction.
2. It recognizes q+1>0 and structuralY>=0, so there is no exponent/nonnegative-layercake gap. Both are retained in the independent expected type.
3. It requests the exact disk-bound normalization. The pinned stdGaussian_complex_closedBall_le_radius_sq_half signature in ScalarUniformSmallBall.lean is the squared-radius/2 bound forstdGaussian(C), exactly the source used here. Squared distance is identified with radius sqrtx by a checked set equality; the variance2 convention is explicit. No properCN1 law is substituted.
4. It verifies the final factorial/power-of2 arithmetic matches; there is no missing factor.
5. It discusses subadditivity and confirms the nonzero-factor inequality, but asks whether the imported lemma is proved. The full proof complexNegativeLog_mul_le is in ComplexGaussianRootNegativeLog.lean, including explicit zero-factor branches. It is a source/olean-locked checked dependency. The new finite-product inequality then follows by finite induction; Cauchy–Schwarz retains multiplicity.
6. It incorrectly replaces totalized complexNegativeLog0 with an extended infinity, and conjectures the algebraic factorization needsP!=0. The actual definition is max(0,-Real.log||z||), withReal.log0=0. The imported splits/evaluation/cardinality identities quantify all complex polynomials, including0; the final universalP proof type passes without an extra premise. ZeroP has zero leading coefficient, empty roots and natDegree0; factorization0=0*1 is valid. No claim about extended-real log integrals is made.

No blocking mathematical issue remains in these scoped warnings after exact-definition/signature checks. This is an author disposition, not blanket model endorsement and not human approval.

[需人工审查] Weighted layercake/Tonelli, Gamma and planar Gaussian normalization, root multiplicities, inherited measure arguments and future physical-model correspondence remain. Finite multivariable/proper scaling and singular-spectrum log-square bridges are still future work at this checkpoint. Frozen manuscript/PDF/upload/code archives unchanged; fullLake/mathlib and independentLinuxkernel NOT_RUN.
