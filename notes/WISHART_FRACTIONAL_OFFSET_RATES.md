# Fractional mean-square and variance bounds

Four public declarations in two modules extend the inverse-square rate to fractional orders. Let0<alpha<=1 and K=E(lambdaPlus inverse)^(2alpha). Under the exact theorem746 condition b=0 or r-b=m or2alpha<|m-r|+1, K is finite. Put A_t=(n/alpha)*t^(-alpha). For every t>=1 the original same-source full-logdet offset and variance satisfy

    E E_t^2 <= A_t^2*K,
    |Var(logdet(I+tX^HX))-Var(S)| <= A_t^2*K+2*A_t*sqrt(K)*sqrt(Var(S)).

These are MSE O(t^(-2alpha)), L2 and variance-difference O(t^(-alpha)) upper bounds, with displayed finite coefficients. Since |m-r|+1>=1, taking any0<alpha<1/2 meets the moment condition for every fixed model with R>0, including square critical models. The endpoint alpha=1/2 is not claimed when its inverse first moment fails. These bounds are not optimal critical asymptotics.

The deterministic core is log(1+x)<=x^alpha/alpha, proved from concave-power subadditivity and log y<=y-1. The positive-mode offset is bounded by alpha inverse*(t inverse)^alpha*(lambda inverse)^alpha. Zero modes vanish exactly and are treated separately. The original-source min-positive witness, squared error integrability, spectral identity, theorem746 and751 supply the stochastic steps. No Gaussian projection is redone and no new limit exchange is used.

Before source, seed2026102241 supplied1323 scalar/finite-spectrum/Gamma-shape1 controls, calibrated on Gamma(1-2alpha) for strictly subcritical2alpha<1. A negative control catches omission of1/alpha at alpha=.1,x=1e6. Finite quadrature is not an endpoint divergence proof. All four initial and final statements exit0 under default heartbeat budget/standard3axioms. Deprecation/linter hints in the finite source are nonblocking and do not alter the proof.

## Real Qoder P4 resolution

Full final source reviewed by Qwen3.8-Max with tools disabled, no independent compilation; response retained. Human review remains required.

1. The finite file asserts only pointwise inequalities. The actual source explicitly obtains integrability of the inverse2alpha moment from746 and uses the already integrable square error in integral_mono_ae. Real rpow is measurable; no stochastic obligation is silently assigned to the deterministic file.
2. All-zero or empty spectra produce zero error and a valid possibly loose upper bound. The actual theorem assumes R>0 and uses a genuine AE positive minimum. A fictional minimum is never supplied for R0.
3. The pinned `Real.rpow_add_le_add_rpow` in Mathlib.Analysis.MeanInequalitiesPow explicitly permits both bases>=0 and0<=p<=1. The source imports it directly and checks x=0 as well. No strict base positivity was omitted.
4. The fixed-rank existential returns exactly i0.val+1=min(m,stackrank) with i0 in the same Fin(card(Fin n)); hr and hi identify it with i. omega constructs a kernel checked arithmetic proof and cannot silently prove a false equality. Literal types bind the exact boundary.
5. The review's claimed completeness requirement for intersecting AE events is false. The AE filter is closed under finite intersections for every measure; no completeness of Gaussian or underlying measurable space is needed. Both events use the same original2mp source. No unverified claim that a Borel Gaussian measure is complete is adopted.
6. The exact751 generic variance bound has absolute value and only two MemLp hypotheses on a probability space. It centers internally and assumes neither zero nor equal means nor independence. The current hUM/hSM provide precisely those premises.
7. The existing square-L1 error theorem explicitly holds for every t>=1; that endpoint is part of its already checked signature. ht0 is used for scalar factorization, not to replace a missing strict endpoint premise.

[需人工审查] ProperCN1 source/variance convention, fixed means and AE rank/index, real inverse powers, integral/variance interpretation and paper mapping. Frozen paper/PDF/upload/code archives unchanged; full Lake/mathlib and independent Linux kernel NOT_RUN. Optimal critical asymptotics and general pseudo-inverse-trace high-scale first/second correction coefficients remain OPEN.
