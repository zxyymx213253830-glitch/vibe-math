## P4 Adversarial Review: CandidateActualTraceTransform.lean

**1. Critical Type Error in `actualNoncentralGram_trace_laplace` (Mathematical Gap)**

The hypothesis `hv (j : Fin n) : -s < 1` is proved via `linarith` from `hs : 0 ≤ s`. However, `linarith` deduces `-s ≤ 0`, which only implies `-s < 1` if Lean's linear arithmetic implicitly handles strict inequalities from non-strict ones correctly here. While `-s ≤ 0 < 1` is mathematically true, the bound `-s < 1` is suspiciously weak for a Laplace transform convergence condition; typically one requires the real part of the parameter to satisfy a strict inequality tied to the support of the measure. If the downstream lemma `actualNoncentralDiagonalGram_integral_exp` genuinely only needs `-s < 1`, this is valid but suggests the lemma itself might be under-specified or the convergence condition is being artificially bypassed by restricting to `s ≥ 0` without ensuring integrability at the boundary.

**2. Missing Positivity/Integrability Justification (Mathematical Gap)**

For `s = 0`, the integral reduces to the total mass of `stdGaussian`. The RHS becomes `1⁻¹ * exp(0) = 1`. This implicitly assumes `stdGaussian (ComplexSample m n)` is a probability measure (total mass 1). The file header states "no joint-spectrum law claim" and restricts to "equality of scalar transforms only," but does not explicitly assert that `stdGaussian` is normalized. If `stdGaussian` is merely a Gaussian reference measure with unnormalized density, the `s=0` case fails. The assumption `hs : 0 ≤ s` includes the boundary where integrability and normalization matter most.

**3. Dimension Mismatch / Silent Coercion Risk in Second Theorem (Mathematical Gap)**

In `candidate_actual_trace_laplace_equal`, the candidate ensemble is indexed by `Fin L → ℝ` with parameters `p L q : ℕ`, while the actual side uses `ComplexSample (m := p+L+q) (n := p+L)`. The mean-matching hypothesis `hmean` equates the squared Frobenius norm of `M` to `∑ lambda j`. However, `lambda : Fin L → ℝ` has length `L`, while `M` has `(p+L+q)*(p+L)` entries. The theorem treats `L` as both the spectral parameter count and implicitly as part of the matrix dimension indexing, but there is no constraint ensuring that the candidate ensemble's effective degrees of freedom match the complex Gaussian model's dimensions beyond the scalar mean equality. If `mixedCandidateEnsemble_trace_laplace_closed` was proved under different dimensional assumptions (e.g., requiring `L = p+L` or similar), this application would be semantically invalid despite type-checking.

**4. Algebraic Simplification Fragility (Minor Gap)**

The step `simp only [sub_neg_eq_add] at hp he h` rewrites `1 - (-s)` to `1 + s` inside products and sums. The subsequent `ring` call in `he` must handle the rational function identity pointwise. While algebraically correct over ℝ, if any denominator `(1+s)` were zero (impossible here since `s ≥ 0`), the field simplifications would be unsound. This is safe but relies on `s ≥ 0` excluding `s = -1`, which is guaranteed by `hs` yet never explicitly cited as preventing division-by-zero in the `simp`/`ring` pipeline.

**5. API/Signature Concern (Not a Mathematical Gap)**

The use of `congr 2; congr 1; ring` at the end assumes the two closed-form expressions are definitionally or propositionally equal after rewriting. This is standard but brittle if upstream normalizations differ by constant factors.
