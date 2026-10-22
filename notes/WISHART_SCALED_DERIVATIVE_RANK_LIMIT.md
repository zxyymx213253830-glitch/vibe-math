# High-scale expected derivative and curvature recover generic rank — 2026-10-22

For the same fixed model X=ZB+M (properCN1 Z:m-by-p, arbitrary fixed complex B:p-by-n and M:m-by-n), define the actual full-matrix expected logdetF(rho) onpositive scale. Six new Codex declarations prove

    rho F'(rho) -> R,
    -rho^2 F''(rho) -> R,
    R=min(m,rank stacked[B;M]),       rho -> +infinity.

Every finite shape, including all zeros, is included. The rank may be deficient; no inverse moment, fullrank, log-integrability or spectral-gap premise is added for these limits. Parameters B,M are fixed; no convergence rate or uniformity over changing parameters is asserted. This does not follow by formally differentiating an asymptotic expansion. Instead it uses the exact already proved derivatives and a bounded spectral-power limit.

The reusable scalar theorem assumes only a FINITE measuremu, measurable f>=0AE, and a strictly positive natural exponentk:

    integral (rho*f/(1+rho*f))^k -> integral indicator(f>0).

It does NOT require fL1 or finite inverse moments. On the eventual nonnegative-parameter tail the integrand is between0 and1; the constant1 is integrable precisely because the measure is finite. The pointwise limit is1 wheref>0, and0 wheref=0 andk>0. The k>0 premise is essential: at a zero mode the k=0 power is1 by0^0=1. Negative scalar parameters are not used for domination; the totalized rational function is nonetheless measurable for every real parameter, even at denominatorzero. No continuity through denominatorzero is asserted.

Finite spectral summation and the checked positive-mode-count=rank identity then yield, for everyk>0, SUM_i E[(rho lambda_i/(1+rho lambda_i))^k] ->R. The k=1 andk=2 specializations identify the scaled first derivative and curvature using the earlier exact derivative formulas; multiplication by a fixed scalar is moved through the Bochner integral with the corresponding standard identity. The two actual limits are consequences of one bounded-spectral mechanism, not six independent probability discoveries.

Fixed-seed2026102206 controls run200000 properCN1 samples and43 checks: independent scalarExp1 closed forms fork1,2; monotonic bounds/limits of finite spectra with empty/zero modes fork1,2,3,7; sampled rank1 high-scale limits; and negative controls detecting an omittedk>0 hypothesis or an omittedrho scaling. Controls are NOT general proofs.

## Final-source P4 and dispositions

A real bounded Qoder Qwen3.8-Max request supplied the full exact final source, tools/MCP disabled, zero retries, without independent compilation. Source snapshots and request/prompt/raw/receipt hashes are preserved. Final leaf and six independent literal target types pass the shared serial Lean gate with standard three axioms. Initial implementation failures were pointwise function-division elaboration/limit normalization and beta reduction before algebra; failed logs are retained and excluded from acceptance. No final-source bytes changed after the P4 snapshot.

1. Qoder alleges unconditional measurability and eventual domination are incompatible for negative parameters. False: they are separate DCT hypotheses. Real division is totalized and measurable onR, including at zero denominator; this does NOT imply continuity there. The proof supplies measurability for all parameters, a stronger valid statement, but the bound only on the filter tailrho>=0. It never claims that the constant1 dominates negative-parameter integrands. The measurable-space structure is fixed and independent ofrho.
2. It conjectures the finite-measure instance forstdGaussian might be absent. The physical ComplexSample is a finite-dimensional REAL Euclidean source, with the existing stdGaussian probability instance; probability implies finite measure. The actual application and independently locked type check elaborate that exact instance, without an undeclared premise. No new Gaussian law is introduced.
3. It conjectures the spectral dimension could be other thann. The checked definitions have complexSampleMatrix z:m-by-p, B:p-by-n, M:m-by-n, so X:m-by-n and X^H X:n-by-n. actualCorrelatedEigenvalue uses Fin(Fintype.card(Fin n)) exactly. Rank-deficient and wide cases legitimately include zero eigenvalues; the positive-mode count formula removes them. No truncation or rank-dimension identification is assumed.
4. It asks whether the imported derivative results establish differentiation under the integral. Their exact definitions and complete proofs are recorded in ExpectedLogDetDerivative.lean and ExpectedLogDetCurvature.lean, with the explicit L1 domination described in their review packets. HasDerivAt of the EXPECTED statistic already states the required derivative of the integral; it is not a pointwise-only derivative claim. The new proof uses those established results rather than exchanging derivative/integral again. These dependencies are source/olean hash locked and retain [需人工审查] status for the human interpretation.
5. It conjectures hidden fullrank premises in the AE generic-rank theorem. Its actual signature quantifies arbitrary fixed B,M of the displayed shapes, with NO fullrank/dimension positivity premise, and gives min(m,rankB+rank(M restricted kerB)). The separately checked matrix_fromRows_rank_eq identifies the sum with rank stacked[B;M]. Both exact signatures are used in the source and pinned in the dependency lock. Fixed parameters remain explicit; nothing is inferred for SNR-dependentB,M.

No mathematical blocking issue remains from these scoped warnings after checking the exact dependencies and quantifiers. This is an author disposition, not blanket Qoder endorsement or human approval.

[需人工审查] DCT, AE generic rank, differentiation-under-integral dependencies, variance and physical/channel/paper interpretation remain. No channel coding theorem, original generalT1 identity, joint/noncentral spectral density or general sharp central coefficient simplification is added. FullLake/mathlib build and independentLinuxkernel remain NOT_RUN; frozen paper/PDF/upload/code archives unchanged.
