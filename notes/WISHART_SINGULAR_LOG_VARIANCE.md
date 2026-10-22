# Fixed singular-factor positive-spectrum logarithms have finite variance — 2026-10-22

For the actual physical model X=ZB+M with properCN1 Z:m-by-p and arbitrary FIXED complex B:p-by-n, M:m-by-n, define

    S(z)=SUM_i (if lambda_i(z)>0 then log lambda_i(z) else0),
    lambda_i eigenvalues ofX^H X.

Three new Codex declarations prove true integrability ofS^2, true integrability of each positive-spectrum log mode squared, and integrability of(S-ES)^2 with

    E[(S-ES)^2]=E[S^2]-(ES)^2.

All finite dimensions, including zeros, and rectangular/singular/zero factors are included. No fullrank, spectral-gap, inverse-moment or noncentral-density premise is added. positiveSpectrumLog is NOTmax(0,loglambda): logs of positive eigenvalues below1 remain negative. The zero eigenmodes contribute0 by the explicit definition. The result asserts a FINITE variance; its general value is not evaluated in closed form. No CLT, fluctuation distribution or mean-square convergence of the high-scale logdet offset is proved at this checkpoint.

## Domination and the fixed witness

The previously checked generic-rank/minor witness selects one FIXED rank-sized coordinate minorD(z), nonzeroAE, with rankX(z)=R=min(m,rank stacked[B;M]) AE. Its log-square is integrable by the newly proved physical holomorphic-polynomial result. The existing deterministic all-zero-mode-aware bound is

    |S| <= T + |log(R!)| + 2|log||D||||,  T=SUM_i lambda_i=traceGram.

This is NOT an assertion that the minor's eigenvalues equal the full matrix's nonzero eigenvalues. The minor determinant is bounded byR! times the coefficient of degreeR ofdet(I+tGram); that coefficient equals the product of the nonzero Gram eigenvalues. Positivity and logarithm identities then give the bound. Injective column selection, exact rankR and nonzero minor are the explicit premises, and the proof supplies the latter two on a common AE set. No eigenvector alignment is required. The old factorial bound remains sufficient even though an exact all-minor expansion is now available; accepted old sources are not altered just to remove a harmless constant.

Squaring and finite Cauchy–Schwarz give

    S^2 <= 3T^2+3|log(R!)|^2+12(log||D||)^2.

The trace-square is already truly integrable from the actual correlated Gaussian moment theorem. The other terms are a constant and a fixed compressed polynomial log-square. This closes the aggregateS-squareL1 result. Each mode follows from the earlier deterministic bound |positiveLog(lambda_i)|<=T+|S|, then its square<=2T^2+2S^2. The centered formula is an ordinary real integrable expansion under a normalized probability measure, using the previousS-L1 and newS-squareL1. It is not an extended-real infinity convention.

## Controls and verification

Fixed-seed2026102209 controls use200000 properCN1 samples and35 tests. Rank1 models with one noisy column have lambda~Gamma(m,1), m1,2,3, so meanlog=digamma(m) and variance=trigamma(m). A singular rank2 factorB=[1,0] plus a fixed noiseless columnc e2 givesS=2logc+log|z1|^2 and variancepi^2/6. Zero/empty/deterministic models and the negative-log-sign convention are included. High-scale squared-error controls and independentExp1 quadrature are saved for a futureL2 convergence target; those controls do NOT prove that target. All controls are implementation evidence, not general proofs.

The final source and three independent literal expected types pass the same serial Windows Lean gate with only standard three axioms. The lock binds full source, inherited project definitions/oleans, pinned toolchain/manifest and the type checker. The initial centered-integral rewrite failure is retained; explicit typed local integrability functions fixed its implementation without changing a target assumption. No source bytes changed after final P4 snapshots.

## Qoder P4 dispositions

A real bounded Qoder Qwen3.8-Max final-source P4 returned with tools/MCP disabled and no independent compilation. Full source/request/prompt/raw/receipt hashes are retained. Its alleged gaps are resolved against exact imported signatures and definitions:

1. Claimed critical zero-mode/minor-alignment gap: false. `hne` is precisely nonzero determinant of the fixed coordinate minorAE; `actualCorrelatedRank_eq_generic_ae` is separately used to supply rank=R. The invoked abs_positive_log_sum_le_minor_log takes these premises and column injectivity. Its proof passes through the rank coefficient/product of nonzero eigenvalues as described above, not a supposed spectral bijection between the minor and the whole matrix. positiveSpectrumLog0=0 is definition-level and requires no extra witness premise. The full sum therefore excludes zero contributions exactly.
2. Claimed missing probability normalization: stdGaussian on this finite-dimensional REAL ComplexSample is the existing normalized Gaussian probability measure, with its static IsProbabilityMeasure instance. It is not an unnamed unnormalized Gaussian-weighted reference measure. Integral constants simplify using that probability instance. The theorem need not expose a new hypothesis asking a caller to prove a static property of this named distribution. The same normalized law is used in every trace/log witness dependency and the independent expected type.
3. Claimed possible complex-valued eigenvalue/coercion gap: the exact definition in CorrelatedLogDetLowScale.lean has codomainR and indexFin(card(Fin n)); Hermitian eigenvalues there are intrinsically real for EVERYz. measurable_actualCorrelatedEigenvalue is measurability of that R-valued function; positive-spectrum comparison and log are both real. There is no AE coercion or assumed realness to supply.

The reviewer recognizes the square domination arithmetic and individual-mode reduction as sound given the imported bound. No mathematical blocking issue remains after these scoped dispositions; this is the author's assessment, not blanket model approval or human review.

[需人工审查] Fixed witness/null-set/rank correspondence, polynomial square-log transport, L2 domination, probability normalization, physical variance and paper/channel interpretation remain. FixedB,M only; no uniformity over parameters. Frozen paper/PDF/upload/code archives unchanged; completeLake/mathlib and independentLinuxkernel NOT_RUN.
