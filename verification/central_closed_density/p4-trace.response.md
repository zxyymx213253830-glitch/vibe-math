## Review of P4: `complexWishart_trace_law`

**1. Hidden target-law assumption in `stdGaussian_half_norm_sq_law` application**
The final `exact stdGaussian_half_norm_sq_law (m * n) ...` assumes the prior was stated for a *specific* constructed space `E` with `finrank = 2*(m*n)`. But `ComplexSample (m := m) (n := n)` is definitionally `Fin (2*m*n) → ℝ`. The proof must verify that the Gaussian measure on this concrete function space coincides with the abstract `stdGaussian E` in the prior. If the prior quantifies over all `E` with dimension `2k`, this is fine, but the instantiation `k := m*n` requires `2*k = 2*m*n`, which the `simp` discharges. No logical gap, but the dependency chain should be explicit about whether `ComplexSample` carries the correct inner product structure matching the prior's `E`.

**2. Variance-one complex entry convention**
The docstring flags `[需人工审查]`. The algebraic identity `complexSampleGram_trace_half_norm` proves trace.re = ‖z‖²/2 where `z` is the *real* source vector with `2*m*n` standard normal coordinates. Each complex entry `(z₀ + i·z₁)/√2` has variance `(1+1)/2 = 1`, so `𝔼[|entry|²] = 1` and `𝔼[trace] = m*n`. This is consistent with `Gamma(shape=m*n, rate=1)` having mean `m*n`. No factor-of-2 gap confirmed.

**3. Finite-sum index order in `complexGram_trace_re`**
The `rw [Finset.sum_comm]` swaps `∑ i, ∑ j` to `∑ j, ∑ i`. This is valid for finite sums unconditionally. However, verify that `complexGram X` (which is `X * Xᴴ`, an `n×n` matrix) has diagonal entries indexed by `j : Fin n` summing over `i : Fin m`. The current statement sums `i : Fin m` outer, `j : Fin n` inner, yielding `∑ᵢ ∑ⱼ ‖X i j‖²`. For an `m×n` matrix `X`, the Gram `XᴴX` vs `XXᴴ` matters. Confirm `complexGram` definition matches the index order here—if `complexGram X = XᴴX` then trace is `∑ⱼ ∑ᵢ |Xᵢⱼ|²`, requiring the swap. Correct as written if `complexGram := X * conjTranspose X` (yielding `m×m`).

**4. Rectangular shapes and `hmn : 0 < m*n`**
The condition `0 < m*n` correctly excludes degenerate cases. For `m ≠ n`, the Wishart is singular when `m < n`, but the trace law remains `Gamma(m*n, 1)` since it depends only on total degrees of freedom. No issue.

**5. Measure-theoretic compositionality**
`Measure.map_map` requires measurability of both maps. `measurable_complexSampleGram` is cited; `fun A => A.trace.re` is continuous hence measurable. Valid.

**Verdict:** No concrete mathematical errors found. The variance convention checks out. The primary human-review item is confirming `complexGram` definition aligns with the double-sum index order (point 3), and that the `stdGaussian_half_norm_sq_law` prior's space `E` instantiates correctly to `Fin (2*m*n) → ℝ` with standard inner product.
