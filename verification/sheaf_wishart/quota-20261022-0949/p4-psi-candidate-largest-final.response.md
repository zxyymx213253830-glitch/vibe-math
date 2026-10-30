## P4 Adversarial Review: `PsiCandidateLargestCDF.lean`

**1. Fubini application without integrability discharge (Theorem 1).**
`setIntegral_compl` requires the integrand to be integrable on the full space. The proof cites `(mixedEnsemble_pair_moment ...).1`, which presumably supplies this, but the integrability is never explicitly named or verified against the exact signature expected by `setIntegral_compl`. If `.1` returns a weaker condition (e.g., mere measurability or an ENNReal-finite bound rather than `Integrable`), the complement-splitting step is unsound. This is an **actual gap** unless the dependency's `.1` projection literally produces `IntegrableOn`.

**2. Restrict-restrict rewriting drops the measure context (Theorem 1).**
`Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hx)` rewrites `∫ y in Ioi x, ... ∂μ` into an unrestricted integral, but `hx : 0 ≤ x` only gives `Ioi x ⊆ Ioi 0` when combined with the implicit fact that `Ioi` is antitone. The direction is correct, yet the rewritten goal shows no `∂μ` at all—just a bare integral. If Lean's coercion interprets this as `∂volume` rather than `∂μ`, the equality is false on the negative half-line. Verify the target measure after `simp`/`rw`.

**3. Determinant factorization via `det_mul_row` (Theorem 2).**
`Matrix.det_mul_row` extracts a product of *row* scalars. The matrix is constructed as `fun i j => psiTailColumnFactor ... j * M i j`, meaning the scalar depends on the **column** index `j`, not the row. Applying a row-factorization lemma to a column-scaled matrix is a semantic mismatch. Either a transpose argument or `det_mul_column` is needed. As written, this is a **concrete mathematical error**.

**4. Nonnegativity proof divides before establishing nonzero denominator (Theorem 3).**
`div_mul_cancel₀ _ (ne_of_gt hd)` uses `hd : 0 < det(...)` from `mixedEnsemble_momentMatrix_det_pos`. However, `hd` is derived under hypotheses `hl : StrictMono lambda` and `hlp : ∀ j, 0 < lambda j`, while the division `hr` is formed using `ENNReal.toReal_nonneg` on a ratio whose denominator involves the same determinant. If the moment matrix determinant is `+∞` in ENNReal (possible for unbounded measures on `Ioi 0`), `.toReal` truncates and the algebraic cancellation `div_mul_cancel₀` does not recover the original value. The gap: no finiteness proof for the determinant appears.

**5. Product positivity assumes each factor is strictly positive (Theorem 4).**
`Finset.prod_pos` requires every factor `> 0`. For `inl a`, the proof is `simp [psiTailColumnFactor]` with no further argument. If `psiTailColumnFactor` can be zero for some parameter configuration consistent with `hl`/`hlp`, the product is zero and the subsequent `field_simp` (which divides by this product) is invalid. The `inr b` branch works, but the `inl` branch is an **unresolved obligation**.

**6. `abs_of_nonneg` applied to ENNReal.toReal (Theorem 4).**
Both `hn` and `h0` are determinants shown `≥ 0` as reals, but they originate from ratios involving `.toReal`. If either numerator was `⊤` in ENNReal, `.toReal = 0`, making the determinant zero and the absolute-value removal trivially correct but the overall ratio `0/0`-undefined. No guard prevents this degeneracy.
