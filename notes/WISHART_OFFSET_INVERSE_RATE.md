# Quantitative high-scale mean-square offset bound

Three public declarations in two modules: a scalar inverse bound, a finite nonnegative spectrum bound, and its actual fixed-model integral consequence. For the original ZB+M model let r=rank stacked[B;M], R=min(m,r)>0, and lambdaPlus be the fixed positive boundary. Write S=sum positiveSpectrumLog(lambda_j) and E_t=logdet(I+tX^HX)-R log t-S.

If rankB=0 or r-rankB=m or2<|m-r|+1, theorem746 gives a finite inverse second moment. For every t>=1 the new explicit bound is

    integral E_t^2 <= (n*t inverse)^2 * integral (lambdaPlus inverse)^2.

Thus the mean-square error is O(t^-2), equivalently the L2 norm is O(t^-1), with a finite explicit coefficient. This is a quantitative result beyond the previous mean-square convergence. It is not asserted when inverse-square integrability is critical or fails, and the factor n is deliberately the safe spectrum size rather than an unproved sharper factor R.

The scalar identity on x>0 is positiveModeOffsetError(x,t)=log(1+t inverse*x inverse), bounded between0 and t inverse*x inverse. For x=0 the offset error is exactly0. The fixed min-positive witness bounds every positive mode; zero modes are handled separately. The resulting squared pointwise bound is integrated with the previously established square-L1 error and theorem746's inverse-square majorant. No new DCT or exchange of limits is used.

Before source, seed2026102239 supplied72 spectra including empty/all-zero/structural-zero cases and scalar x=2, plus Gamma shape3/4 inverse-square quadrature calibrated on1/((k-1)(k-2)),807 checks total. Scaled Gamma mean-square errors approach0.5 and1/6 from below. Shape2 inverse-square divergence is excluded analytically, not inferred from a finite cutoff. Controls are not proofs.

## Real Qoder P4 resolution

The complete final two sources were reviewed by Qwen3.8-Max, tools disabled, no independent compiler. Original response retained. Human review remains required.

1. `positiveSpectrumLog x` explicitly equals `if0<x then Real.log x else0`. Both it and the mode offset vanish at x=0 by their definitions. The x=0 branch is source-unfolded and kernel checked; no unguarded analytic inverse is used there.
2. The finite bound is intentionally an upper bound using card(ι). All-zero spectra give LHS0 and a nonnegative RHS, including emptyι where RHS0. The actual theorem has R>0 and a genuine positive boundary, so its a is not an arbitrary surrogate for a nonexistent positive minimum. Tightness at zero is not claimed.
3. The exact fixed-rank witness returns i0:Fin(Fintype.card(Fin n)), the same type as i, and its boundary equals min(m,stackrank). hr and hi identify their values, with no implicit casts. Literal target and final kernel checks validate the exact index types.
4. Both the min-positive witness and generic-rank event explicitly use stdGaussian(ComplexSample(m:=m)(n:=p)). Their finite intersection is on precisely the same source; neither is a reduced or pushed-forward Gaussian event.
5. Real integral_mono_ae requires the supplied integrability of both real functions and the AE inequality, not a further nonnegativity premise. Both functions here are nonetheless nonnegative squares, and hz.1 gives positive minimum while hz.2 gives the lower bound for every positive mode. No inverse property is inferred at a zero minimum. Totalized real functions remain measurable globally and exceptional null sets do not affect the integral.
6. The card-to-n reduction and natural squares are explicit in the checked proof; mul_pow closes the exact expression. The literal checker also locks the complete coefficient and measure. No extra factor or informal coercion is hidden.

Failed finite scalar v1 left the second positiveSpectrumLog conditional unsimplified and used a positivity tactic on a1<=1+nonnegative goal. v2 explicitly simplifies both guards and uses a nonnegative-product inequality. Failed source/log retained, default heartbeat budget unchanged. Actual source v1 and both final checks exit0.

[需人工审查] ProperCN1 variance/source, fixed means, AE spectral identity, integral domination, and paper interpretation. Full Lake/mathlib and independent Linux kernel NOT_RUN; frozen publications unchanged. Quantitative variance difference and fractional-exponent critical-regime rates remain separate OPEN goals.
