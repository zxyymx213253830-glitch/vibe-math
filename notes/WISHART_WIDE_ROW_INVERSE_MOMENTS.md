# Wide IID fixed-mean row-Gram inverse moments

2026-10-22, Codex. Let X=Z+M, with Z:m-by-n independent proper CN(0,1),
M fixed complex, 0<m<=n. Let ell be the least eigenvalue of X X^H, explicitly
implemented as gramSmallestValue X^H. For every real p>0,

    Integrable ell^(-p) under complexGaussianMatrixLaw M
      iff p<n-m+1.

For p>=n-m+1, the nonnegative ENNReal lower integral is TOP. This is not a
claim that Lean's totalized real-valued Bochner integral equals infinity.
Zero inverse values on null sets follow the same totalization as the old tall
theorem. The full-rank actual Gaussian dependency guarantees row Gram is
positive definite almost surely, via adjoint law and the old tall full-rank
law. No coordinate is chosen on a rank-zero space; m=0 is excluded. Square
m=n is included and has threshold1. Structural zero eigenvalues of X^H X for
n>m are not used as the minimum in this statement.

The proof reuses the checked tall criterion for arbitrary fixed mean and all
positive real exponents, first under the full matrix measure and then through
the actual adjoint pushforward law with mean M^H. It does not repeat a tail or
Fubini proof. The critical/higher lower-integral statement follows from
nonnegative measurability and the iff criterion. This supplies the wide IID
block ingredient; arbitrary singular/rectangular noise factor B, canonical
block Gaussian independence and the general singular threshold remain OPEN.
The exact link to a fixed smallest-positive coordinate of the original wide
column Gram is a separate transport step; do not identify its ordinary last
eigenvalue with this row minimum.

Controls: wide_row_inverse_control.py, seed2026102220, 18 rectangular/fixed-mean
matrices plus four central one-row Gamma fractional-moment references and the
critical local log-divergence and wrong-column-minimum controls:42 checks.
The Gram characteristic-polynomial identities are exact complex-rational;
the Gamma comparison is numerical against Gamma(n-p)/Gamma(n). Controls are
not a general integrability proof. The new Lean source passed on its first
gated check with standard three axioms. Both independent literal types and
the immutable final leaf also passed.

Real Qoder Qwen3.8-Max P4 reviewed the full final source, tools disabled,
08:36:40--08:37:07UTC, exit0. It labels an alleged dimension mismatch critical
and then explicitly confirms the swap n,m, the fixed mean M^H, and all
hypotheses match. Its contradiction warning is likewise self-resolved in the
same response; raw response is retained. The remaining measurability note is
discharged by continuity of finite-dimensional conjugate transpose and the
already checked measurable minimum. The reviewer concludes no mathematical
gap found; that is scoped model review, not human approval or independent
compilation. No source changes after review.

[需人工审查] Inherited real-power/Fubini/nonnegative-integral/measure-law and
properCN1 physical-model interpretation remain required. Frozen publications
unchanged; full Lake/mathlib and independent Linux kernel NOT_RUN.
