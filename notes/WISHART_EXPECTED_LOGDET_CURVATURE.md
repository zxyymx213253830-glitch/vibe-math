# Expected full-logdet curvature and exact strictness — 2026-10-22

For fixed complex B:p-by-n and M:m-by-n, let X=ZB+M, where Z is m-by-p with independent proper complex CN(0,1) entries, physically built from2mp standard REAL Gaussian coordinates divided by sqrt2. Let lambda_i be the nonnegative ordered eigenvalues of X^H X and

    F(rho)=E log(Re det(I+rho X^H X)),
    D(rho)=SUM_i E[lambda_i/(1+rho lambda_i)],
    K(rho)=SUM_i E[(lambda_i/(1+rho lambda_i))^2].

The previous checkpoint already proved F'=D onrho>0. New results prove

    D'(rho)=F''(rho)=-K(rho),   rho>0.

The squared resolvents are truly integrable. F is concave on(0,infinity) for all finite dimensions. With deterministic generic rank R=min(m,rank stacked[B;M]), F is strictly concave on that interval IF AND ONLY IF R>0. If R=0, F(rho)=0 for everyrho>=0. No fullrank, inverse moment or positive-dimension premise is introduced. These are properties of the full matrix statistic with natural logarithms; no channel-coding, mutual-information identification, capacity normalization or growing-parameter uniformity is proved.

## Why a first moment suffices

The scalar integration theorem allows an arbitrary measure mu, including infinite measures. Its only moment hypothesis is fL1, alongside measurable f and f>=0AE. Around a fixedrho>0, for everyx>rho/2,

    0 <= (f/(1+x f))^2 <= (2/rho) f.

The dominating function is integrable by the first-moment premise. The parameterized dominated-derivative API then CONCLUDES integrability of the squared resolvent and the derivative formula. It does not require fL2 or inverse moments. The actual finite spectral sum instantiates this interface using previously proved eigenvalueL1. Strictness uses the positive integral of the nonnegative K integrand; the existing actual generic-rank AE theorem ensures at least one positive mode AE wheneverR>0. No new Gaussian density assumption is needed for this step beyond the already established AE rank result and the nonzero probability measure.

The zero-rank branch derives every eigenvalue=0 from the positive-mode count=rank identity, uses the pointwise full-logdet spectral identity, and integrates0. Necessity in the iff statement is checked using points1,2,3/2 and weights1/2: a constantzero function cannot be strictly concave onIoi0.

## Verification and scope

Codex authored thirteen printed declarations in ExpectedLogDetCurvature.lean (5) and ExpectedLogDetStrictConcavity.lean (8). These include scalar/deterministic tools and do NOT represent13 independent probability breakthroughs. Independent literal target definitions retain all quantifiers, the arbitrary-measure scalar interface, positive-scale conditions, and exact rank criterion. The final-source lock binds project definitions/source/olean dependencies, pinned toolchain/manifest and the independent checker. All checks use the existing shared Windows serialgate; only the standard three axioms are accepted. Initial implementation failures (division inequality direction, function extensionality/quotient normalization, zero-function reduction and projection argument elaboration) remain archived; only final successful leaves enter the audit.

Fixed-seed2026102205 controls use200000 proper-CN1 samples and34 checks. The scalarExp1 derivative and curvature are compared against independent exponential-integral closed forms. A singular factor B=[1,0] plus a fixed noiseless column tests positive rank2 curvature, finite differences, strict Jensen inequalities and scaled-derivative approach to rank. Empty/zero shapes and wrong-sign negative control are included. Controls are implementation evidence, NOT general proofs. The scaled-derivative asymptotic was only a control in this bundle and is NOT a new theorem here.

## Real Qoder collaboration and P4 dispositions

The bounded real P1 supplied three strictness routes. We used the negative-second-derivative route. Its statement that density is needed anew to get positive-mode support is stronger than necessary: the separately proved deterministic generic-rank AE identity and a nonzero probability measure already supply it. Its broad phrase that there are no extra assumptions for DCT must be read with finite measure for a constant1 bound; the scalar derivative-exchange result itself uses the integrable f bound and permits arbitrary measure.

The final-source Qoder Qwen3.8-Max P4 response is substantive, with tools/MCP disabled and no independent compilation. Full source snapshots, request/prompt/raw/receipt hashes are preserved. No source bytes changed after this review. Its warnings and author dispositions:

1. Claimed possible index mismatch: actualCorrelatedEigenvalue is explicitly defined with index Fin(Fintype.card(Fin n)) in CorrelatedLogDetLowScale.lean:21. The per-index theorem uses exactly that type, and the sum domain is inferred from the same function. No identification of different abstract finite sets occurs. Independent literal expected types use the same family; the finite-sum function extensionality step only changes a sum of functions into a function of a sum.
2. The reviewer explicitly withdraws its proposed simultaneous-AE derivative concern: the proof first fixes the ONE AE set wheref>=0, then for each such sample proves the derivative for ALLx>rho/2. The denominator ispositive throughout that set. This is precisely the domination API's quantifier order.
3. Claimed missing eventual derivative equality: the source explicitly constructs he by filtering the neighborhoodIoi0 and applying the imported HasDerivAt theorem at EACH positive nearbyx, then `.deriv`. Existence of HasDerivAt at every nearby positive parameter yields the asserted derivative value there, not merely at the basepoint. Squared-resolvent integrability is separately concluded by integral_resolvent_hasDerivAt; it is not assumed or missing.
4. Claimed AE rank lifting needs a fresh rank-measurability proof: false as stated. The imported theorem already asserts the exact AE predicate; `filter_upwards` applies logical implications on that AE set and does not require that every predicate involved be a newly established measurable map. The K integrand IS measurable and L1, independently proved from measurable eigenvalues. Integral strictness uses its integrability plus an AE positivity statement and the nonzero probability measure. The older AE rank proof is based on checked polynomial null-set witnesses; its inherited measure/model interpretation remains [需人工审查].
5. The review finds the zero-rank/strictness arithmetic correct but speculates about future negative-parameter changes. Both definition and theorem types are hash/type locked; strict concavity is explicitly onIoi0, and zero evaluations use nonnegative parameters. No negative-scale extension is claimed.
6. The review confirms no hidden dimensional positivity or fullrank hypotheses. The actual fixed generic rank is the only strictness condition.

No blocking mathematical issue remains from this scoped review after the above dispositions. This is not blanket Qoder approval and not human review.

[需人工审查] Differentiation under the integral, measure/null-set/positive-integral arguments, Gaussian variance and physical/model/paper correspondence still require human review despite kernel checks. Full Lake/mathlib build and Linux independent Lean compilation remain NOT_RUN. Frozen paper/PDF/upload/code archives unchanged.
