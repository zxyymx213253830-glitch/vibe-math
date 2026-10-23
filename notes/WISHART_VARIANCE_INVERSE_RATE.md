# Variance difference with an explicit inverse-square coefficient

The generic probability-space statement proves, for u,v in L2 and I=integral(u-v)^2,

    |Var(u)-Var(v)| <= I+2*sqrt(I)*sqrt(Var(v)).

No independence is assumed. Center u,v, apply the already checked second-moment difference inequality, identify the centered error second moment as Var(u-v), then use Var(u-v)<=integral(u-v)^2. Constants do not alter variance.

For the original fixed ZB+M model, define S as the positive-spectrum log sum and K=E(lambdaPlus inverse)^2. Under the exact finite-inverse-square condition from746, the actual logdet satisfies for every t>=1

    |Var(logdet(I+tX^HX))-Var(S)|
      <= (n/t)^2*K+2*(n/t)*sqrt(K)*sqrt(Var(S)).

The explicit finite coefficients give an O(t^-1) variance difference bound, alongside749's O(t^-2) mean-square offset error. This is not claimed in regimes where inverse-square integrability fails. Existing MemLp/variance-limit results establish the finite log-spectrum variance; no fresh limit exchange or unproved uniform integrability is introduced.

Before source, seed2026102240 tested72 finite weighted probability models/365 checks including non-independent errors, deterministic variance shifts, and tight centered two-point examples u=(1+epsilon)v. These controls are not proofs. The prior offset807 controls are reused. Two public declarations/two modules are counted, one generic inequality and one actual-model consequence.

## Real Qoder P4 resolution

Qwen3.8-Max reviewed both complete final sources, tools disabled/no independent compile. It reported no blocking mathematical gap. Full response retained; human review still required.

1. MemLp includes AEStronglyMeasurable as part of its data; hu.sub(memLp_const...) and hv.sub(...) provide complete centered L2 hypotheses to the imported second-moment bound. `variance_eq_integral hu.aemeasurable` likewise supplies its exact measurable premise. No additional unproved inference is needed.
2. `integral_square_difference_bound` is explicitly the real L2 statement used here, on arbitrary measures, with exactly the two MemLp hypotheses. The final source and literal target check bind this API and norm convention; the current probability space is a permitted special case.
3. The review's shorthand assertion uc-vc=u-v is not true without equal means. The proof instead explicitly identifies uc-vc=e-integral(e), using the integrable-sub formula; hJ is therefore Var(e), not integral(e^2). The subsequent inequality Var(e)<=integral(e^2) is separately proved from the probability variance formula. This distinction is retained rather than adopting the review's shorthand.
4. R=min(m,r) is deterministic because r is the fixed stacked matrix rank. U subtracts the fixed scalar R log t, and variance_sub_const applies exactly to it. No random-rank centering is used.
5. The fixed boundary i+1=min(m,r)>0 and accepted generic-rank theorem give AE positivity. The moment condition gives K finite through749's integrable inverse square. Nonnegative square-root and coefficient factorization are explicit in the kernel checked proof. K and Var(S) are repository real integrals/variance with the displayed source.

Both initial sources and final locked checks exit0 at default heartbeat budget/standard3axioms. [需人工审查] Original properCN1 source and variance, AE index, L2/centering/integral meaning and paper mapping. Frozen publication artifacts unchanged; full Lake/mathlib and independent Linux kernel NOT_RUN. Fractional-exponent critical-regime rates remain OPEN.
