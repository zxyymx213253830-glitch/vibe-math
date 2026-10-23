# Critical second high-scale coefficient

Codex proof bodies; original fixed properCN1 model on the same 2mp real Gaussian
source. Let r=rank stacked[B;M], b=rank B, R=min(m,r), and kappa=|m-r|+1.
Assume R>0, b>0, r-b<m and kappa=2. The boundary index is fixed by i.val+1=R.
Let S=sum positive eigenvalue logs and L=sum totalized spectral reciprocals
(zero eigenvalues contribute zero). Then L is integrable and

    t*(E L-t*(E logdet(I+t XHX)-R log t-E S)) -> real atTop.

Every finite-scale expectation here is finite. This is divergence of a real
function of t, not a Bochner real integral assigned infinity. It does not prove
an optimal logarithmic coefficient or any matrix pseudoinverse identity.

The generic finite-spectrum theorem first proves a lower-integral limit at TOP
from an infinite lower integral of half the reciprocal-square sum. The actual
model proof establishes that infinite integral by contradiction: finite integral
would imply integrability of the minimum reciprocal square, contradicting the
already checked exhaustive inverse classification at the critical exponent2.
It then uses the AE rank identity, a nonnegative finite-scale gap, integrability
of L/logdet/S, and exact expectation linearity to recover the real limit.

Controls seed2026102245 precede source: 48 finite checks, including Gamma(2,1)
closed E1 formula, deterministic finite-coefficient negative control, and zero
mode controls. Finite controls are not a divergence proof. The first actual
source failed on an unresolved sum element type; failed-v1 source/log are
retained unaccepted. Explicit sum types fix it; v2 passes with standard3axioms.

## Real cross-family P4 resolution

The complete final sources were supplied to one bounded Qoder Qwen3.8-Max P4,
tools disabled, exit0. Preserve the full response and receipt. No approval retry.

1. Claimed missing nonnegativity for Fatou is rejected. The integrands supplied
   to lintegral_liminf_le have type ENNReal, produced by ofReal; nonnegativity is
   built into that type. The generic theorem does not convert a signed real
   integral. The actual real-integral conversion separately proves AE
   nonnegativity through criticalSecondModeNonneg and hNN.
2. Claimed missing real convergence/boundedness is rejected. hs' explicitly has
   Tendsto of a REAL finite sum to a REAL finite reciprocal-square sum. It
   follows from the imported scalar real Tendsto, including x=0. Composing with
   globally continuous ENNReal.ofReal gives ENNReal convergence and hence its
   liminf. Eventual positivity is not a prerequisite for this continuous map.
3. Claimed infinite real inverse at zero and inverse measurability gap is
   rejected. In Lean's real field inv_zero=0; this is deliberately a totalized
   spectral inverse. Real inverse is globally Borel measurable, and the scalar
   limit theorem explicitly covers zero. No inverse at zero is infinity here.
4. Imported classification has exactly three alternatives:
   b=0 OR r-b=m OR q<kappa, under hr,hR,hi,q>0. All those exact hypotheses are
   supplied in hQTop. hb excludes the first, hcm excludes the second, hk and
   q=2 exclude the last. No extra hidden full-rank premise is discarded.
5. The AE rank substitution is sufficient. lintegral_congr_ae is used explicitly
   for the spectral equality. The exact Bochner bridge requires Integrable F
   and 0<=AE F, precisely hFI and hNN. Its signature does not require everywhere
   nonnegativity, and no completeness of the underlying measure is inferred.
6. The reviewer confirms expectation linearity is fully supported by hLI,hC,hS,
   integrable_const and hE.const_mul. Retain that confirmation with the response.

The independent literal checker matches both complete theorem types. Final
source/dependency/toolchain/checker hashes are locked, with serial shared-gate
kernel checks. Model review is not human review or independent compilation.

[需人工审查] Fatou/filter assumptions, AE source/rank/spectrum, inverse moment
classification, expectation identities and original-paper interpretation.
FullLake and independent Linux kernel NOT_RUN. Frozen publications unchanged.
