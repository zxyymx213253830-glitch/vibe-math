# Positive spectrum aggregate-log bridge — 2026-10-21

Four Codex declarations in PositiveSpectrumLogIntegrability.lean provide a deterministic domination, a generic L1 implication and a conditional actual correlated-matrix logdet offset. They do not prove the aggregate logarithmic moment for arbitrary singular Gaussian factors.

For a finite nonnegative spectrum f, let T=sum f and S=sum positiveSpectrumLog(f). Since h(x)=positiveSpectrumLog(x)<=x, all gaps f_j-h_j are nonnegative. The single-gap inequality gives h_i>=f_i-T+S>=-T-|S|. The other side is h_i<=f_i<=T<=T+|S|. Hence |h_i|<=T+|S|. Integrable coordinates and integrable S imply each h_i is L1, for an arbitrary measure; no finite-measure assumption is introduced. The actual-model theorem explicitly assumes aggregate L1.

Qoder Qwen3.8-Max supplied a real final-source P4 response, 20.19 seconds, with tools disabled and no independent compilation. Its alleged cancellation gap is false: the final two linarith invocations use hn i, neg_le_abs S for the lower side, and hu i, hs, abs_nonneg S for the upper side. These hypotheses are present in the exact reviewed source. No source change was made to answer this warning. The review's incidental claim that Integrable itself requires sigma-finiteness is also incorrect; the stated arbitrary-measure implication is retained. The reviewer correctly confirmed that hSum remains explicit.

The fixed-seed 200000-sample controls cover spectra of sizes0..8 and a cancellation-only negative control. They are sanity checks, not proofs. Literal independent target types and final leaf checks use the same serial Windows Lean gate; standard axioms only. Native SHEAF indexing is not independent compilation.

[需人工审查] AE lifting, integrability domination and the interpretation of actualCorrelatedEigenvalue remain explicit human-review obligations. Full Lake/mathlib build NOT_RUN. Frozen manuscript, PDF and upload archives unchanged.

The remaining substantive bridge is to establish aggregate positive-spectrum-log L1 from a nonzero fixed compression and a proved spectral comparison, or from a real-source determinant-coefficient polynomial with a separate real-Gaussian polynomial log theorem. Planar-complex log L1 cannot simply be restricted to the real axis. Arbitrary complex polynomial roots need not occur in conjugate pairs. Qoder's earlier P1 suggestion is only a route and does not discharge these obligations.
