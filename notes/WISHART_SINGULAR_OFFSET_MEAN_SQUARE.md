# Actual singular-factor logdet offset converges in mean square — 2026-10-22

Let X=ZB+M under the same actual properCN1 source, with fixed arbitrary compatible complexB,M. LetC_r(z)=log(Re det(I+r X^H X)), R=min(m,rank stacked[B;M]), andS(z)=the sum of loglambda over strictly positive eigenvalues, with zero modes assigned0. Four new Codex declarations in two modules prove

    E[(C_r-R log r-S)^2] -> 0,     r -> +infinity,

and true integrability of that squared error for everyr>=1. All finite dimensions and rectangular/singular/zero factors are included. This is convergence of RANDOM statistics in mean square on ONE shared Gaussian sample space; it is stronger than the already established convergence of their expectations. It is not obtained by differentiating or squaring an expectation limit.

There is no fullrank, spectral-gap or inverse-moment premise, and no explicit error rate, CLT or parameter uniformity claim. The preceding checkpoint establishedS-squareL1 and finite variance, which this proof uses. Convergence of the variance ofC_r itself is not yet a theorem of this checkpoint; that requires a further second-moment/centering argument.

## The reusable mechanism

For x>=0 define

    e(x,r)=log(1+r x)-indicator(x>0)*log r-positiveSpectrumLog(x).

Forr>=1, the exact scalar bound is0<=e(x,r)<=x+|positiveSpectrumLog(x)|. Ifx>0, rewrite the error aslog(x+1/r)-logx; it is nonnegative, tends0 by continuity oflog atx, and is bounded above using1/r<=1 andlog(1+x)<=x. Ifx=0 the error is identically0. No positive value is artificially imposed at a zero mode.

For a finite nonnegative measurable familyf_i under an ARBITRARY measuremu, square-L1 off_i and ofpositiveSpectrumLog(f_i) imply

    (SUM_i e(f_i,r))^2
       <= card(I) SUM_i [2 f_i^2+2 positiveSpectrumLog(f_i)^2],   r>=1.

The right side is truly integrable by hypothesis. The new general theorem therefore proves integrability on that tail AND the squared-error integral tending0 by dominated convergence. It does not assume finite/probability measure; the majorant has no unexplained constant needing finite mass. An empty index set gives0 directly.

The physical specialization supplies actual eigenvalue squares and positive-log squares from separately checked results. The deterministic spectral identity and positive-mode count=rank identity show that the finite sum of scalar errors equalsC_r-rank(X)logr-S pointwise. On the existing common AE generic-rank set, rank(X)=R, so replacing the random count with the fixedR is legitimate. The theorem keepsB,M fixed throughout.

## Evidence and P4

The already saved fixed-seed2026102209 experiment (200000 samples/35 controls) includes rank1Gamma and singular rank2 actual models, independentExp1 quadrature for the squared offset error, and zero/empty/deterministic models. Those previously future-target controls are now paired with this separate general proof. They remain controls, not proofs or a fitted rate.

All final leaves and four independent literal expected types pass the shared serial Windows Lean gate with only standard three axioms. The source definition ofe, full headers, project definitions/oleans, pinned toolchain/manifest and expected-type checker are hash locked. Initial failed logs record scalar inequality elaboration, constant-function/measurable-predicate inference, and a finite-sum rewrite orientation; final checks correct implementations without weakening hypotheses. No final source bytes changed after P4 snapshots.

A real Qoder Qwen3.8-Max final-source P4 used exact full sources, disabled tools/MCP and zero retries, with no independent compilation. Its raw response is preserved. It calls most of its own headings non-issues after examining the proof. The remaining dispositions are:

1. Pointwise convergence needs onlyr>0 eventually for the logarithmic identity; the uniform bound usesr>=1 eventually. These are distinct valid requirements. A theorem about a limit alongatTop has no missing globalr>=1 assumption; the actual DCT proof explicitly uses that tail.
2. Measurability at a fixedr treatslogr as a real constant and is valid for allr. The review's statement thatReal.logr=0 for everyr<=0 is false: onlyReal.log0=0, while negative arguments followmathlib's absolute-value convention. Nothing in the proof uses that false statement; negative scales are outside the eventual domination and physical spectral substitution.
3. The reviewer confirms the square/absolute-value identities and the2x^2+2log^2 bound are valid.
4. Its rank-AE concern is explicitly withdrawn: insidefilter_upwards, hz is the pointwise specialization. The checked stacked-rank identity and casts are then used exactly.
5. Its alleged substantive natural-versus-real count mismatch is false against the exact dependency. gram_positive_modes_eq_rank is explicitly `(SUM_i if0<lambda_i then(1:R)else0)=(X.rank:R)`. It ALREADY states a REAL equality, not a natural-count equality. The change step only unfolds actualCorrelatedEigenvalue to that same family; no numeric-to-real coercion is inserted into a proof of a natural equality. hc.transhR is real transitivity throughout. The source/olean dependency lock and independent expected type retain these exact types.
6. The pointwise actual full-logdet spectral signature matches the call withr>=1, so no joint density, rank/fullrank or hidden positivity hypothesis is assumed.

No mathematical blocking issue remains after checking these exact definitions/quantifiers. This is an author disposition, not blanket model approval or human review.

[需人工审查] Dominated convergence, AE rank/null-set transport, physical variance and model/paper interpretation remain. positive-spectrum log includes negative values for0<lambda<1. Frozen paper/PDF/upload/code archives unchanged; fullLake/mathlib and independentLinuxkernel NOT_RUN.
