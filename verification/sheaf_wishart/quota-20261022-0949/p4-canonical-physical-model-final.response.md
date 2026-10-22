## P4 Adversarial Review: `CanonicalPhysicalModel.lean`

### 1. Mathematical Gap: Ill-Formed Block Extraction (Critical)

The theorem `canonical_physical_sample_block_law` concludes with an equality involving `.toBlocks₁₁` and `.toBlocks₂₁` applied to the result of `canonicalSumRowAction`. However, `canonicalSumRowAction` returns a `Matrix (Fin a ⊕ Fin c) (Fin b ⊕ Fin c) ℂ` (inferred from the identity theorem's RHS which is a `fromBlocks` construction over these sum types).

**Problem:** There is no mathematical definition provided for `.toBlocks₁₁` or `.toBlocks₂₁` on a matrix already indexed by sum types. If these are projections onto the `(Fin a) × (Fin b)` and `(Fin c) × (Fin b)` sub-blocks respectively, they must be explicitly defined as such. As written, applying block-extraction operations to a matrix that is *already* decomposed into blocks via its index type `(Fin a ⊕ Fin c) × (Fin b ⊕ Fin c)` is semantically ambiguous. The identity theorem proves the full matrix equals a `fromBlocks` construction; the law theorem then silently extracts components without specifying what `.toBlocks₁₁/₂₁` means on this type. This is not an API question—it is a gap in the logical specification of the map being pushed forward.

### 2. Missing Non-Degeneracy Assumption on `N` (Critical)

The block identity constructs a matrix with lower-right block `N : Matrix (Fin c) (Fin c) ℂ`. The RHS of the identity is:
```
fromBlocks (...) 0 (...) N
```
This is a deterministic algebraic identity. However, the subsequent **law** theorem claims the pushforward measure equals `(complexGaussianMatrixLaw A).prod (complexGaussianMatrixLaw H)`, which is supported only on the `(a × b)` and `(c × b)` blocks corresponding to positions 11 and 21.

**Problem:** The identity shows the full `(a+c) × (b+c)` transformed sample has lower-right block exactly `N` (deterministic, no noise term appears there since `Z*U` lands only in the first `b` columns via `hBT`). But the law statement projects only `.toBlocks₁₁` and `.toBlocks₂₁`, discarding the 12 and 22 blocks. This marginalization is valid **only if** the projection map is well-defined (see point 1) and the resulting measure ignores the constant `N` block. However, no assumption states that `c > 0` or that `N` is consistent with the support of the Gaussian law. If `c = 0`, the sum type degenerates; if `c > 0`, the deterministic block `N` carries Dirac mass that must be marginalized out correctly. The formal statement does not account for the measure-theoretic interaction between the fixed `N` block and the extracted components.

### 3. Implicit Use of Imported Law Without Signature Verification (Moderate)

The proof of `canonical_physical_sample_block_law` terminates with:
```
exact actual_sum_isometric_noise_block_law U hU V A H
```
after rewriting via the pointwise identity.

**Problem:** The rewrite `he` produces a lambda returning a pair of functions (the 11 and 21 blocks with `+A i j` and `+H i j` shifts). The imported theorem `actual_sum_isometric_noise_block_law` is then invoked to identify this pushforward as the product of shifted Gaussians. However, without seeing the signature of this imported theorem, we cannot verify it accepts the **pair** structure produced here rather than a single augmented matrix. The semantic match between the rewritten goal (a product-space-valued map) and the imported theorem's conclusion (presumably about joint laws) is asserted, not demonstrated. If the imported theorem produces a joint law on a single matrix rather than a product measure on a pair, the `exact` will fail to close the goal semantically even if Lean accepts it via definitional equality hidden behind noncomputable instances.
