# Expected full-logdet derivative at positive scale

Codex proved a generic derivative-under-integral theorem for an arbitrary measure mu and measurable f>=0 AE with f L1. At every r>0, f/(1+r f) is L1 and

`d/dr integral log(1+r f) = integral f/(1+r f)`.

No finite-measure assumption is added. The local parameter set is the entire positive half-line; the derivative bound `0<=f/(1+x f)<=f` holds uniformly for every x>0. The integrable majorant f does not depend on x. The pinned parametric-integral theorem concludes both derivative integrability and the derivative formula from these premises.

For the actual properCN1 model X=ZB+M, fixed arbitrary rectangular/singular/zero B,M and all finite dimensions, the finite spectral sum and existing actual eigenvalue L1/measurability give

`d/dr E log(Re det(I+r X^H X)) = SUM_i E[lambda_i/(1+r lambda_i)]` for r>0.

The expected full determinant statistic is used on the left, including its singular modes through I+r Gram; no log of a singular unshifted Gram determinant is taken. Each summand is integrable before the sum/integral exchange. The theorem does not assert differentiability at r=0, concavity, a coding theorem or a new information-estimation identity. The previous right derivative at0 and fixed-parameter high-scale offset remain separate results.

Eight fixed-seed2026102203/200000-sample controls compare the scalar exponential(1) derivative with the exact E1 reference, finite differences using shared samples and deterministic spectra including zero. They are controls, not proofs.

The first Qoder response raised the derivative-integrability API premise and then qualified it as depending on the exact signature. The actual pinned Analysis/Calculus/ParametricIntegral.lean theorem has Integrable(F' r) as a conclusion, not an extra premise; its supplied integrable bound and measurability derive it. Its initial uniform-domination alarm is withdrawn in the same response; f bounds the derivative on all positive parameters, without deterioration near0. Its statement that finite sums alone make an integral exchange automatic is too loose; the source explicitly supplies integrability for every log summand. A final exact-API review request includes the actual signature and unchanged final source, superseding an irrelevant scope sentence inherited in the first request template. No source change was needed for these warnings. Model review is not human review or an independent compiler run.

The exact-API response returned in30.13seconds. It raises and then withdraws its first three alleged errors. Its remaining objection is conditional on actualCorrelatedMatrixLogDet_eq_spectral being AE-only. The exact pinned CorrelatedLogDetLowScale.lean signature takes every individual source z and nonnegative x and gives ordinary equality; no rank or AE premise appears. Thus funext is applied to a genuine pointwise equality, and the eventual positive-parameter neighborhood is explicitly supplied. The derivative conclusion is a SUM of integrals, exactly what HasDerivAt.sum returns; no unproved equality to a differently specified derivative integrand is required. The imported pointwise spectral identity and complete final type were compiled and checked. The raw conditional alarm is preserved, not called human approval.

[需人工审查] Differentiation under the integral, AE nonnegativity, spectral measurability, integral/sum exchange and physical covariance/variance correspondence. Full Lake/mathlib and Linux kernel builds NOT_RUN; frozen publication unchanged. No parameter-uniform statement or remote push.
