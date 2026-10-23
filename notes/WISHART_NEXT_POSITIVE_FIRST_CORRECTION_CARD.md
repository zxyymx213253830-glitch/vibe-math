# General positive-spectrum first high-scale coefficient after755

Accepted755/94cffe3, auditPASS/facade106 realexit0,83 acceptance records: arbitrary fixed-model inverse classification746; inverse-square MSE/variance rates749/751; fractional rates755 with0<alpha<=1 and finite inverse2alpha. Anyalpha<1/2 covers every R>0 fixed model, but endpoint/optimal critical asymptotics are not claimed. Do not redo completed rate proofs.

Next target: for R=min(m,rank stacked[B;M])>0 and finite minimum-positive inverse first moment (b0 or r-b=m or1<|m-r|+1), prove

    t*(E logdet(I+tX^HX)-R log t-E S) -> E sum_j(lambda_j inverse).

Zero modes use totalized reciprocal0 in the sum; with AE positive-rank selection this is the positive-spectrum reciprocal sum. Do not assert an ordinary full-matrix inverse or a pseudoinverse matrix identity unless separately proved. The existing CorrelatedNoiselessFirstCorrection covers only the uniform-floor row model, not arbitrary singular factors.

First scalar statement for all x>=0: t*positiveModeOffsetError(x,t)->x inverse. For x>0, reuse scaled_log_inverse_first_correction_bounds from NoiselessRowFirstCorrection and the exact positive-mode/log(1+(t*x)inverse) identity; squeeze its nonnegative gap by1/(2*t*x^2). x=0 has both sides0. A t>0 eventual set is sufficient; default heartbeat budget only.

For the actual expectation, use the original same2mp source, theorem746 at q=1, fixed min-positive witness and actual square/log integrability. The reciprocal sum is measurable and bounded AE by n*lambdaPlus inverse. The scaled offset t E_t is nonnegative and bounded by the same integrable majorant using finiteSpectrumOffsetError_nonneg_le_min_inverse, t*t inverse=1. Prove pointwise convergence of the finite sum using the scalar limit, and invoke tendsto_integral_filter_of_dominated_convergence. Its measurability premise is eventual, so t>=1 integrability of physical logdet minus deterministic Rlogt minus S suffices.

Use the exact spectral offset identity already present in749/755; a private pointwise helper parameterized by the actual rank equality can prevent duplicating it in the bound and limit steps. For the expectation expression, use integral_sub with all explicit L1 hypotheses, probability integral_const, and integral_const_mul. [需人工审查] DCT, null sets, real inverse and source/model mapping. No uniformity in varying B,M is claimed.

Before source, fixed-seed finite spectra including zero modes and calibrated scalar Gamma2/Gamma3 controls must verify scaled error tends to the known inverse first moments1 and1/2; finite quadrature is not a proof. Keep critical Gamma1 outside finite-inverse assumptions. Later a second coefficient under inverse second moments can reuse scaled_log_inverse_second_correction_bounds and a half-quadratic dominating gap, but it is a separate goal.

Same serial session/library/compute.lock gate; no direct/concurrent Lean, active source edits, lock deletion or stopping others. Codex proofs, real bounded Qoder P4/full final source and exact types; audit/facade/acceptance and own commits/no push. Frozen publication artifacts unchanged; full Lake/mathlib and independent Linux kernel NOT_RUN. Human review and original T1/G2/paper mapping remain open.
