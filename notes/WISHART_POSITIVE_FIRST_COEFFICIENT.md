# General expected positive-spectrum reciprocal first coefficient

For arbitrary fixed B,M on the original same2mp properCN1 source, set r=rank stacked[B;M], R=min(m,r)>0, S=sum positiveSpectrumLog(lambda_j), and L=sum(lambda_j inverse), with zero modes contributing0. Under the exact finite inverse-one condition b=0 or r-b=m or1<|m-r|+1, the new theorem proves L integrable and

    t*(E logdet(I+tX^HX)-R log t-E S) -> E L.

This identifies the first high-scale expectation coefficient for arbitrary singular factors, beyond the older uniform-floor row result. It needs only inverse first moment finiteness, not inverse square. L is a spectral reciprocal sum; no ordinary inverse of a singular full Gram, nor an unproved matrix pseudoinverse identity, is asserted.

The scalar theorem covers x>=0 and proves t*positiveModeOffsetError(x,t)->x inverse, with zero mode exactly0. The positive branch uses the checked Taylor gap0<=x inverse-t log(1+(tx)inverse)<=1/(2tx^2). The actual proof keeps one original source, proves the fixed minimum gives an integrable bound n*lambdaPlus inverse for both L and the scaled nonnegative error, and uses dominated convergence with explicit eventual measurability. Expectation linearity is separately justified by L1 inputs and probability integral_const.

Controls seed2026102242,60 finite spectra/731 checks including zeros and Gamma shape2/3 calibrated inverse first moments1 and1/2, precede source. Critical Gamma shape1 is excluded from the finite-coefficient control, and quadrature is not a general proof. Two public statements/two modules are counted.

## Real Qoder P4 resolution

Full final source reviewed by Qwen3.8-Max with tools disabled/no independent compilation; original response retained. Human DCT/model review remains required.

1. `scaled_log_inverse_first_correction_bounds` explicitly concludes the pair0<=x inverse-t log(1+(tx)inverse) and the displayed half-quadratic upper bound. The new `.1` is exactly the nonnegative lower squeeze premise, rewritten by the checked scalar identity. The upper constant/t limit is separately supplied. No division is evaluated at t=0: eventual t>0 is used for all algebra and bounds.
2. harg:0<1+(t*x)inverse is proved from t>0,x>0 by a kernel checked positivity proof; harg.ne' is exactly the nonzero hypothesis needed for Real.log_mul. This succeeds in both initial accepted and final source checks, not an assumed tactic result.
3. The fixed-rank existential returns i0.val+1=min(m,stackrank) with the identical Fin(card(Fin n)) type. hr and hi force identical natural values; Fin.ext proves index uniqueness. It returns a fixed rank boundary, not an arbitrary minimum-value witness with a possibly different index. The literal target checker locks the exact i and rank hypotheses.
4. The reviewer explicitly agrees AE domination is sufficient. Both hMin and hRank use the same original measure. DCT receives the AE bound and the L1 majorant hI.const_mul n; it never demands all-sample rank stability.
5. L's measurability, nonnegativity, AE norm domination and the majorant's L1 are all supplied before mono'. The review finds no gap in this step. Positivity of the selected minimum holds AE under R>0; totalized reciprocals of structural zeros contribute0 to L.
6. The t>=1 event implies t>0 for the private spectral identity, and eventual integrability/measurability suffices for DCT. The final expectation rewrite explicitly supplies both integral_sub premises and expands the same local measure alias.

Failed scalar v1 passed the full pair instead of its first projection; failed actual v1/v2 exposed inverse-name ambiguity, a redundant closing tactic, literal integral-sub arguments and local measure alias normalization. All failed versions/logs are retained unaccepted; final scalar v2/actual v3 and locked types/source checks exit0 at default heartbeat budget, standard3axioms only. Unused-tactic/deprecation hints are nonblocking.

[需人工审查] Actual variance normalization, AE rank/index, dominated convergence/linearity and paper interpretation. Frozen publication artifacts unchanged; full Lake/mathlib and independent Linux kernel NOT_RUN. General inverse-second-moment second coefficient, and divergent first coefficient in the critical inverse-one regime, remain OPEN.
