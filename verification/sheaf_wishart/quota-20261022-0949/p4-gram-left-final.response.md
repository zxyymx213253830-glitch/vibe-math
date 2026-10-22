## P4 Adversarial Review: GramMinimumLeftComparison.lean

**1. Mathematical gap: `matrixColumnControl` applied to inverse requires justification (gramSmallestValue_mul_left_lower)**

The upper bound theorem uses `matrixColumn_energy_bound T`, which presumably states that for any vector v, ‖T*v‖ ≤ matrixColumnControl T * ‖v‖. The lower bound theorem applies the upper bound to `T⁻¹`, yielding a factor of `matrixColumnControl T⁻¹`. This is mathematically valid only if `matrixColumn_energy_bound` holds for `T⁻¹` as a matrix in its own right. Since `hT : IsUnit T.det` guarantees `T⁻¹` exists as a matrix over ℂ (via `nonsing_inv`), this should be fine—`matrixColumn_energy_bound` takes an arbitrary matrix. No actual gap here upon reflection, but worth confirming that `matrixColumn_energy_bound` has no hidden assumptions (e.g., requiring the matrix to be expressed as `toEuclideanCLM` of something specific). If it's truly universal over `Matrix (Fin m) (Fin m) ℂ`, this is sound.

**2. Potential semantic mismatch: `matrixColumnControl` of `T⁻¹` vs. inverse of `matrixColumnControl T`**

The lower bound yields `gramSmallestValue A hn ≤ matrixColumnControl T⁻¹ * gramSmallestValue (T*A) hn`. This is **not** the same as `(matrixColumnControl T)⁻¹ * gramSmallestValue A hn ≤ gramSmallestValue (T*A) hn` unless `matrixColumnControl T⁻¹ = (matrixColumnControl T)⁻¹`, which is generally false (the operator norm of an inverse is not the reciprocal of the operator norm). The theorem as stated is correct but weaker than what a reader might expect from "left transformation comparison." This is not a bug—it matches the module header's disclaimer that this does not identify smallest positive eigenvalues under structural zeros—but could mislead downstream users expecting two-sided control with the same constant.

**3. Dependency on `exists_gram_minimum_unit_vector` without rank assumption**

The proof of the upper bound extracts a minimizer `w` via `exists_gram_minimum_unit_vector A hn`. The module docstring explicitly notes "No rank assumption on A," so `A` could have a nontrivial kernel. In that case `gramSmallestValue A hn = 0` and the minimizer `w` achieves zero Rayleigh quotient. The proof still works: `hray` gives `gramSmallestValue (T*A) hn ≤ ‖(T*A)*ᵥ w‖² / ‖w‖²`, and the energy bound gives `‖T*(A*ᵥ w)‖ ≤ matrixColumnControl T * ‖A*ᵥ w‖`. If `A*ᵥ w = 0`, both sides are zero and the inequality `0 ≤ 0` holds. No gap, but the `he : gramSmallestValue A hn = ...` rewrite must produce exactly `‖A.toEuclideanLin w‖²` (or the squared norm form used by `matrixColumn_energy_bound`). If `gramSmallestValue` is defined via Rayleigh quotient normalization and `he` carries a denominator, the `rw [hw, one_pow, mul_one]` cleanup must fully discharge it. This hinges on exact API signatures of the imported module.

**4. `matrixLeft_composition` type-level concern**

The composition theorem asserts `(T*A).toEuclideanLin u = T.toEuclideanCLM (A.toEuclideanLin u)`. The proof uses `ext i` then rewrites to `Matrix.mulVec_mulVec`. This requires that `toEuclideanLin` and `toEuclideanCLM` are definitionally compatible with `mulVec` in the expected way. The `ext i; change ...` step exposes the underlying vector indexing. If `toEuclideanCLM` involves a coercion or different linearity packaging than `toEuclideanLin`, the `change` tactic might not close definitionally. This is an API coherence question, not a mathematical one, but a mismatch here would cause the entire file to fail elaboration rather than just require `sorry`.

**Summary:** No hard mathematical errors detected. The main adversarial concern is item 2: downstream transport using these bounds must not conflate `matrixColumnControl T⁻¹` with `(matrixColumnControl T)⁻¹`.
