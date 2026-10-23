# Fractional offset/variance rates after751

CLOSED at755/94cffe3: both finite majorants and actual fractional MSE/variance bounds are accepted. Next WISHART_NEXT_POSITIVE_FIRST_CORRECTION_CARD.md, not another fractional-rate workflow. Historical plan below retained.

Accepted746: exhaustive fixed singular-model inverse classification including R0 absence. Accepted749/8a91a6f: inverse-square integrability implies MSE offset<=n^2 t^-2 E(lambdaPlus^-2). Accepted751/30e204e: variance difference<= (n/t)^2 K+2(n/t)sqrt(K)sqrt(Var S). Latest auditPASS/facade105 realexit0,81 acceptance records,751 items. Do not redo these results.

Remaining useful extension: handle inverse-square critical regimes via fractional exponents. For0<alpha<=1, aim to prove log(1+x)<=x^alpha/alpha for x>=0. Pinned mathlib `Real.rpow_add_le_add_rpow` is in Mathlib.Analysis.MeanInequalitiesPow: `(a+b)^p<=a^p+b^p` for a,b>=0,0<=p<=1. Combine it at a=1,b=x with `Real.log_le_sub_one_of_pos` applied to `(1+x)^alpha` and `Real.log_rpow`. No new calculus library or full build is needed.

Then positiveModeOffsetError(x,t)<=alpha^-1*(t^-1)^alpha*(x^-1)^alpha, including zero modes explicitly. Finite positive-minimum bound has coefficient `(n*alpha^-1)*(t^-1)^alpha`. For fixed original B,M, R>0 and the existing inverse classification at q=2alpha, target

    E E_t^2 <= ((n/alpha)*t^-alpha)^2 E(lambdaPlus^-2alpha).

Assume the exact moment condition b=0 or r-b=m or2alpha<|m-r|+1. Since the threshold is always>=1, this includes every fixed model with R>0 for every0<alpha<1/2; it yields subcritical fractional rates even for the square threshold1 case. Do not claim endpoint alpha=1/2 when its inverse first moment diverges. These are upper bounds, not sharp critical asymptotics.

Reuse749's exact same-source spectral identity, min-positive witness, square-L1 offset and integral_mono_ae. Only replace the scalar bound and the majorant. For squaring, pinned `Real.rpow_mul_natCast hx alpha 2` gives x^(alpha*2)=(x^alpha)^2; keep alpha>0 and nonnegative inverse bases explicit. Statement can retain the coefficient `((n/alpha)*t^-alpha)^2` rather than overcomplicating exponent normalization.

After that, the generic variance bound751 gives `A^2 K+2 A sqrt(K) sqrt(Var S)` with A=(n/alpha)t^-alpha. Reuse751's centering and L2 inputs, not a new covariance proof. A separate universal0<alpha<1/2 corollary may be useful but is not a new probability breakthrough.

Before source, seed-fixed scalar/finitespectrum controls should include zeros and empty shapes, alpha in(0,1], scale sweeps, Gamma shape1 with q=2alpha<1 calibrated on Gamma(1-q), and a negative control showing omission of alpha^-1 fails for large x and small alpha. Finite quadrature is not proof of divergence; never use a cutoff to claim endpoint failure. No source for this extension existed at this card's creation.

Same serial collaborative_check.py gate/session/library/compute.lock; no direct/concurrent Lean, active edits, live-lock deletion, upgrades or stopping others. Codex proofs, real bounded Qoder P4/explicit types/source hashes, audit/facade/acceptance/own commit/no push. [需人工审查] Actual properCN1 source, AE rank/index, inverse powers and integral/variance meaning, paper mapping. Frozen publication artifacts unchanged; full Lake/mathlib and independent Linux kernel NOT_RUN.
