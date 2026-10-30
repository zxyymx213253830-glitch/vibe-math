## P4 Adversarial Review: `PsiCandidateCountPolynomial.lean`

**1. Missing integrability hypotheses in `mixedCandidateCountPolynomial_restricted` (Mathematical Gap)**

The proof applies `setIntegral_compl` to split the integral over `Ioi x` and `Iic x`. This theorem requires the function to be integrable over the entire space. The hypothesis `hI := (mixedEnsemble_pair_moment ...).1` is used, but it's unclear whether `.1` actually asserts integrability over all of `ℝ` or merely over `Ioi 0`. Since the measure `μ = volume.restrict (Ioi 0)` has support `(0, ∞)`, integrability must hold specifically with respect to this restricted measure. If `mixedEnsemble_pair_moment` only guarantees local integrability or integrability on a different domain, the complement splitting is unjustified.

**2. Potential circularity/missing dependency in `mixedCandidateEnsemble_count_tail_polynomial` (Mathematical Gap)**

The proof invokes `mixedCandidateEnsemble_count p L q lambda hl hlp (Ioi x) measurableSet_Ioi k hk`, which computes the ensemble probability for the set `Ioi x`. However, no assumption is stated that `mixedCandidateEnsemble` is defined as a probability measure or that the total measure is finite and normalized to 1. The division by `(mixedCandidateTailMatrix p L q lambda 0).det` implicitly assumes this determinant serves as the correct normalization constant. If `mixedCandidateEnsemble_count` already returns a normalized probability, the division is redundant; if it returns an unnormalized volume, the identity relating the determinant to the total mass must be established elsewhere.

**3. Strict positivity vs. non-negativity mismatch (Minor, Not a Gap)**

`psiCountPolynomial_transport` assumes `hl : ∀ j, 0 ≤ lambda j` and `hx : 0 ≤ x`, while downstream theorems (`mixedCandidateEnsemble_count_eq_psi_coefficient`) strengthen these to `hlp : ∀ j, 0 < lambda j`. The transport theorem itself is valid under non-negativity, but the final coefficient equality requires strict positivity to ensure `d ≠ 0`, `f ≠ 0`, and `z ≠ 0`. This is handled correctly—the stricter assumptions are introduced only where needed—but reviewers should note that `paperPsi_zero_det_signed_transport` is invoked under `hlp.le`, not the weaker `hl`.

**4. Determinant sign tracking through reindexing (Potential Sign Error)**

In `paperPsi_zero_det_signed_transport`, the step `rw [Matrix.det_reindex]` introduces a permutation sign. The subsequent application of `Matrix.det_mul_row` extracts column factors. The interaction between row/column permutations and multiplicative column scaling must preserve the sign correctly. Specifically, `Matrix.det_mul_row` scales rows, but the factors `psiTailColumnFactor` are described as *column* factors. If these are applied via `Matrix.det_mul_column` internally or if the equivalence between row-scaling after permutation and column-scaling before permutation is not exact, a sign discrepancy could arise. The proof relies on `push_cast; rfl` at the end, which suggests the types align, but the semantic correctness of treating column-derived factors through a row-scaling lemma warrants explicit verification.

**5. Polynomial coefficient extraction across ring homomorphism (API Question, Likely Correct)**

The step `simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map] at hc` extracts the `k`-th coefficient after mapping through `Complex.ofRealHom`. This assumes `Polynomial.coeff_map` commutes with scalar multiplication by constants. This is standard for ring homomorphisms applied to polynomials, but depends on `Complex.ofRealHom` being a ring homomorphism (true by construction). No gap here, but worth noting as a dependency on Mathlib's polynomial API coherence.

**Summary:** Two substantive mathematical concerns: (1) the exact integrability condition provided by `mixedEnsemble_pair_moment` relative to the restricted measure, and (2) the implicit normalization claim linking the ensemble count to the determinant ratio without an explicit probability measure axiom.
