# Mathematical Review: Expected Gram Entry for Complex Gaussian Model

## Model Verification

The setup is mathematically sound:
- **Z** (m×p): entries constructed from 2mp real standard Gaussians paired as (X + iY)/√2, yielding iid CN(0,1) with E[Z_ka · Z̄_kb] = δ_ab
- **B** (p×n): arbitrary fixed matrix (rectangular/singular/zero allowed)
- **X** = ZB + M, target: E[(X^H X)_ij] = m·(B^H B)_ij + (M^H M)_ij

The construction correctly produces variance-1 complex normals from the real source measure with covariance I.

## Five Printed Theorems — Mathematical Assessment

**Theorem 1 (`complexGaussianMoment_correlated_row_pair`):**
Evaluates a single row-k contribution. The polynomial expansion into four terms (quadratic in Z/Z̄, linear in Z̄, linear in Z, constant) is correct. Application of L(P) via:
- E[Z_ka · Z̄_kb] = δ_ab collapses the double sum ∑_{a,b} star(B_ai)·B_bj to ∑_a star(B_ai)·B_aj = (B^H B)_ij
- Odd moments E[Z_ka] = E[Z̄_kb] = 0 eliminate linear terms
- Constant term star(M_ki)·M_kj survives directly

Result per row: (B^H B)_ij + star(M_ki)·M_kj. **Correct.**

**Theorem 2 (`complexGaussianMoment_correlatedGramEntryPolynomial`):**
Sums over k ∈ Fin m. The row-sum yields m·(B^H B)_ij + ∑_k star(M_ki)·M_kj = m·(B^H B)_ij + (M^H M)_ij. Uses `Finset.card_univ` and `Fintype.card_fin` for cardinality m. **Correct.**

**Theorem 3 (`eval_correlatedGramEntryPolynomial`):**
Polynomial evaluation identity: substituting actual Gaussian samples into the formal polynomial equals the concrete Gram entry (ZB+M)^H(ZB+M)_ij. This is algebraic verification that the polynomial encodes the intended function. **Correct.**

**Theorem 4 (`integrable_actualCorrelatedGram_entry`):**
Integrability follows from the existing theorem that any polynomial in the Gaussian source is integrable (already proved). Since the Gram entry equals a polynomial evaluation (Theorem 3), it inherits integrability. No Bochner default-zero exploitation possible because the L1 export is explicit. **Correct.**

**Theorem 5 (`integral_actualCorrelatedGram_entry`):**
Combines Theorems 2–4: the integral of the Gram entry equals the polynomial moment, which equals m·(B^H B)_ij + (M^H M)_ij. **Correct.**

## Specific Checks Requested

| Issue | Verdict |
|-------|---------|
| B^H B vs BB^H | Correct: (X^H X)_ij uses B^H B (p×p inner products summed over m rows), not BB^H |
| Double-sum/conjugation | Correct: star on B_ai index a, B_bj index b; δ_ab contracts properly |
| Empty m,p,n | Handled: Fin 0 sums are empty, cardinality 0, formulas give 0 |
| Polynomial L1/actual source | Correct: lives in mp direct/conjugate pairs via Sum.inl/inr encoding |
| Invertibility of B | Not required: no inverse, whitening, or full-rank assumption used |
| L linear not multiplicative | Correct: only linearity and specific moment facts applied, never L(PQ)=L(P)L(Q) |
| P1 errors (E[tr W²] vs E[(tr W)²], source I/2) | Those errors are absent here; this file addresses only expected Gram entry |

## Axiom Compliance

The five `#print axioms` commands should confirm dependence only on the standard three (classical choice, propext, funext) plus the existing library's moment/integrability infrastructure. No additional axioms introduced.

## Human Review Requirements

As specified:
- **Measure/Fubini**: Exchange of finite sums with integration is justified by linearity (finite m, p, n); no infinite-dimensional Fubini needed.
- **Model**: The map from 2mp real Gaussians to Z via /√2 pairing correctly yields CN(0,1) entries with E[Z_ij Z̄_ik] = δ_jk.
- **Numeric verification**: Fixed seed 2026101926, 200000 samples, 5 shapes including identity Gamma and zero B controls — confirms formula empirically before proof.

## Conclusion

All five theorems are mathematically correct for the stated model. The proof strategy (polynomial encoding → row-pair evaluation → summation → integrability transport → integral equality) is valid. No speculative compilation issues; Lean exit 0 expected given proper imports.
