# P4 Review: Concrete Issues

## 1. Critical: `complexVectorGramRankOne` Conjugation Placement (GaussianBartlettFiber.lean)

```lean
def complexVectorGramRankOne {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ := fun j k => star (z j) * z k
```

This produces `(j,k)` entry `z̄ⱼ zₖ`. The standard outer product `zzᴴ` has `(j,k)` entry `zⱼ z̄ₖ = zⱼ star(zₖ)`. The current definition yields the **conjugate-transpose** of the intended rank-one projection. Consequently, `projectedResidualGram` computes `VᴴV + zzᴴ` rather than the residual `VᴴV - zzᴴ`, breaking the Bartlett decomposition's geometric meaning (projection onto the orthogonal complement of `u`).

**Fix**: Change to `fun j k => z j * star (z k)`.

## 2. Dimension Mismatch in Fiber Law (GaussianBartlettFiber.lean)

`centralBartlettFiber_law` states that for fixed `u : EuclideanSpace ℂ (Fin (m+1))`, the fiber law over `V : Matrix (Fin (m+1)) (Fin n) ℂ` equals `(standardComplexColumnLaw n).prod (complexWishart (m := m) (n := n))`.

The Wishart `complexWishart (m := m) (n := n)` is supported on `n×n` matrices with `m` degrees of freedom. However, `V` has **m+1 rows**, not `m`. After projecting out the rank-one component along `u`, the residual Gram should have `m` effective degrees of freedom—this is mathematically correct—but the matrix `matrixRemainingRows (unitaryActColumns U V)` has type `Matrix (Fin m) (Fin n) ℂ`, so its Gram is indeed `n×n` with parameter `m`. **No issue here** upon closer inspection; the types align.

## 3. Missing Mean-Zero Justification (All Files)

The main claim specifies "actual CENTRAL CN(0,1) matrix." All laws are stated at mean `0` (e.g., `complexGaussianMatrixLaw (0 : Matrix ...)`), but the files never explicitly connect this to the general non-central case or document why centrality (mean=0) is essential for the unitary invariance step (`complexGaussianMatrixLaw_unitary_invariant`). This is a **semantic gap** for readers expecting the central assumption to be discharged or documented as a hypothesis.

## 4. Total Division at `u=0` (GaussianBartlettFiber.lean)

`normalizedColumnCoefficients` divides by `(‖u‖ : ℂ)`. The header claims "division interpreted totally at u=0," but the definition uses raw `/` without invoking a totalized division operator. In Lean, division by zero in `ℂ` is defined (returns 0), making the function technically total, but the measurable-map proofs never flag where this convention is used. The null-set argument (`standardComplexColumnLaw_nonzero_ae`) correctly handles almost-sure statements, yet the fiber map `centralBartlettFiber u` at `u=0` returns a degenerate value whose semantic meaning is undocumented.

## 5. Row/Column Indexing Consistency

Verified correct: `matrixColumnSplit` extracts column 0 and shifts via `j.succ`; `matrixRowSplit` extracts row 0 and shifts via `i.succ`. The transpose transport `complexGaussianMatrixLaw_rowSplit` correctly conjugates the column result. **No issue.**

## 6. Variance Convention

`standardComplexColumnLaw` scales by `(√2)⁻¹`, converting real-standard Gaussians (variance 1 per real coordinate) to CN(0,1) (variance 1/2 per real part, total variance 1). The Gamma shape parameter `m+1` in `gammaMeasure ((m+1 : ℕ) : ℝ) 1` matches `‖u‖² ~ Gamma(m+1, rate=1)` for `u ∈ ℂ^(m+1)` with CN(0,1) entries. **Consistent.**

---

**Summary**: Issue #1 (conjugation swap) is a concrete bug affecting the residual Gram's sign. Issue #4 needs documentation. Others are verified correct or flagged as semantic gaps.
