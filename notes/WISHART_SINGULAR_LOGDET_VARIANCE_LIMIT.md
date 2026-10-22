# Full-logdet variance limit for fixed singular factors — 2026-10-22

For fixed arbitrary complex B:p-by-n, M:m-by-n and the actual properCN1 matrixZ:m-by-p, letC_r=log(Re det(I+r(ZB+M)^H(ZB+M))), R=min(m,rank stacked[B;M]), andS=the sum of logarithms of its strictly positive Gram eigenvalues, zero modes contributing0. Four further Codex declarations prove

    E[(C_r-Rlogr)^2] -> E[S^2],
    Var(C_r) -> Var(S),              r -> +infinity.

The actual offset andC_r belong toL2 for everyr>=1. S belongs toL2 by the preceding fixed-singular-factor theorem, so the variance values here are finite and are not artifacts of totalized variance on non-L2 functions. Every finite shape, including zero dimensions/factors, is retained. FixedB,M only; no inverse-moment/fullrank/spectral-gap premise, rate, parameter uniformity or CLT. The limiting variance is identified asVar(S), not evaluated in a general numerical closed form. Natural log units are used; no coding/capacity theorem is derived.

The previous result already proved mean-square convergence C_r-Rlogr ->S on one source space. The new generic second-moment continuity theorem allows any measuremu and uses existing Holder/Cauchy–Schwarz to prove

    |Eu^2-Ev^2| <= E(u-v)^2 + 2sqrt(E(u-v)^2)sqrt(Ev^2),

foru,v inL2. Hence the already established mean-square error limit gives the offset second-moment limit. ItsL2 membership is proved from(U_r-S)+S, not assumed. The mean-offset convergence is the earlier actual expectation theorem plus the checked integral-of-a-constant identity under the normalized Gaussian probability measure.

Finally mathlib's variance_eq_sub applies to the provenL2 functions. Continuity of subtraction/squaring givesVar(U_r)->Var(S); variance_sub_const identifiesVar(U_r)=Var(C_r). These foundations are imported, not claimed as new probability theory. No differentiation of a stochastic asymptotic or informal exchange of square and expectation occurs.

Fixed-seed2026102210 controls use200000 properCN1 samples and33 tests. Rank1Gamma(m,1),m1..3, has known log variance trigamma(m); the singular factorB=[1,0] plus a fixed noiseless column has log variancepi^2/6; zero-rank models are included. Constant-shift variance equality, high-scale offset second moments and variance comparisons are checked; finite discrete probabilities also verify the exact Cauchy bound. The tests assert neither a general rate nor general monotonicity and are not proofs.

The two final leaves and four independent literal expected types pass the shared serial Windows gate, standard three axioms only. Source/definition/project-olean, pinned toolchain/manifest and expected-type hashes are locked. Failed implementation logs (absolute-value triangle lemma name, unavailableMemLp.congr method and explicit natural-rank cast normalization) are retained; final code uses exact function equality and unchanged theorem premises. No source bytes changed after P4 snapshots.

Real Qoder Qwen3.8-Max final-source P4 used exact full sources, disabled tools/MCP, zero retries and no independent compilation. It reports no actual mathematical gaps. It asks only whether MemLp.integrable_sq and Integrable.aestronglyMeasurable APIs exist; both are pinned library results and exercised by the successful final source/type checks. It confirms the Cauchy bound, limit arithmetic, L2-sum algebra and constant-shift variance argument. It flagsR=0 as a degenerate case, already universally included: zero generic rank gives zero statistic and zero variance. It recognizes the rank cast as a real coercion, with no substantive gap. The raw response and exact hashes remain bound. Model review is not human approval.

[需人工审查] Holder/integral algebra, mean-square/moment implications, Gaussian normalization, inherited AE rank and polynomial-log-square transport, and physical/model/paper interpretation remain. Frozen manuscript/PDF/upload/code archives unchanged; fullLake/mathlib and independentLinuxkernel NOT_RUN. Original generalT1 candidate identity, noncentralG2, general central sharp-constant simplification and journalT3/full-paper mapping remain separate open obligations.
