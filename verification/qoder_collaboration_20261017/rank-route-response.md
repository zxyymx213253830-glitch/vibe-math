## Route Comparison

**Route 1: Left Inverse + Restriction of Scalars**
- **Core lemmas:** `nonsing_inv_mul` yields left inverse; `LinearMap.finrank_range_of_inj` gives complex rank n; `finrank_real_of_complex` doubles to 2n; `Submodule.restrictScalarsEquiv` transfers structure; `Submodule.finrank_add_finrank_orthogonal` yields complement 2(m-n).
- **Hidden assumptions:** m ≥ n implicit in det(A^H A) ≠ 0.
- **Failure modes:** Left inverse construction requires explicit nonsingularity witness; restriction-of-scalars equivalence needs careful module-level bookkeeping.
- **Machine-check type:** Pure Lean algebra. Fully formalizable with given assets.

**Route 2: Rank-Nullity**
- **Core lemmas:** Rank-nullity over ℂ gives dim(ker A) = 0 from det(A^H A) ≠ 0; real rank-nullity on restricted scalars.
- **Hidden assumptions:** Requires proving ker(A^H A) = ker(A) first; assumes rank-nullity applies cleanly after scalar restriction.
- **Failure modes:** Kernel equality proof is nontrivial without positive-definiteness; rank-nullity over ℝ after restriction demands extra module-theoretic overhead not directly in assets.
- **Machine-check type:** Lean algebra, but gaps in kernel transfer.

**Route 3: Gram Positive Definiteness / SVD**
- **Core lemmas:** A^H A positive definite ⟹ invertible; SVD gives singular values > 0.
- **Hidden assumptions:** Requires inner product space infrastructure, spectral theorem for Hermitian matrices.
- **Failure modes:** SVD is analytic/numeric, not algebraic; positive definiteness ↔ invertibility requires continuity arguments absent from finite symbolic controls.
- **Machine-check type:** Numeric control. Not feasible with current algebra-only assets.

## Selection

**Route 1 is shortest.** It directly chains the five given assets without auxiliary analytic machinery or kernel-transfer proofs.

## Why This Does NOT Prove Random Gaussian Matrices Are a.e. Full Rank

The deterministic result conditions on det(A^H A) ≠ 0 as a **hypothesis**. Proving a random Gaussian matrix is almost-everywhere full rank requires showing the **singular locus has measure zero**—a statement about the probability distribution over all matrices, not about a single matrix satisfying the hypothesis. Measure-theoretic arguments (absolute continuity of Gaussian measure w.r.t. Lebesgue, polynomial hypersurfaces having zero measure) are entirely outside the scope of these algebraic assets.
