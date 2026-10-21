## Concrete Mathematical Issues

**1. `complexMatrixEntries` variance direction (critical)**

The file asserts that `complexMatrixEntries_law` derives proper CN(0,1) from real coordinates via `(sqrt2)^-1`. However, the integrability theorems in `ActualComplexPolynomialLog.lean` use `rw [← complexMatrixEntries_law m p]` to **pull back** from the product measure to the physical matrix law. If `complexMatrixEntries` maps physical entries *to* the standard product (i.e., multiplies by `sqrt(2)` rather than divides), then the pushforward/pullback direction in `integrable_map_measure ... .mp` is inverted. The source does not show the definition of `complexMatrixEntries` or the statement of `complexMatrixEntries_law`, so it is impossible to verify from these files alone whether the transport goes in the correct direction. This is a concrete gap: an orientation error here would mean the physical variance is 2, not 1/2 per real coordinate.

**2. `entryAffineCompressedDet` dimension mismatch for non-square products**

The polynomial is defined as `(L * (X * B + M) * H).det` where:
- `X : Matrix (Fin m) (Fin p)`
- `B : Matrix (Fin p) (Fin n)` → `X * B : Matrix (Fin m) (Fin n)`
- `M : Matrix (Fin m) (Fin n)` ✓
- `L : Matrix (Fin q) (Fin m)` → `L * (X*B + M) : Matrix (Fin q) (Fin n)`
- `H : Matrix (Fin n) (Fin q)` → final product: `Matrix (Fin q) (Fin q)`

This is well-typed and yields a square determinant. **No issue here** upon inspection—the dimensions compose correctly to a `q × q` determinant for arbitrary rectangular inputs.

**3. Missing `Fintype` instance in `ActualComplexPolynomialLog`**

The theorems `integrable_actualComplexMatrix_holomorphic_negativeLog/log` invoke `properComplex_pi_polynomial_negativeLog_integrable P`, which requires `[Fintype ι]`. Here `ι = Fin m × Fin p`, which has decidable `Fintype`, but the theorem statements do not carry this instance explicitly. Lean's typeclass resolution should find it, but if `m` or `p` are zero, `Fin 0 × Fin p` is empty—this is fine mathematically (empty product = constant polynomial), but worth confirming the kernel accepts `Fintype (Fin 0 × Fin p)`.

**4. `Real.log 0 = 0` totalization consistency**

Both files state `Real.log 0 = 0` (Mathlib convention). The measurability proofs use `(measurable_const.max ...)` for `complexNegativeLog` (which involves `-log ‖·‖`). At zeros of `P`, `‖P‖ = 0`, so `Real.log 0 = 0` and `complexNegativeLog 0 = -0 = 0`. This is consistent. **No issue.**

**5. Polynomial rescaling `Q` is holomorphic**

The substitution `X_i ↦ s · X_i` with `s = (sqrt 2)⁻¹ : ℝ` preserves holomorphicity because scalar multiplication by a real constant is ℂ-linear. Confirmed by `Complex.real_smul` usage. **No issue.**

---

## Remaining Human-Review Limitations

- **Cannot verify** the definition/direction of `complexMatrixEntries` or the exact statement of `complexMatrixEntries_law` from these sources alone.
- **Cannot verify** that `stdGaussian (ComplexSample (m := m) (n := p))` actually produces independent CN(0,1) entries (depends on external `ComplexSample` structure).
- **Cannot verify** the upstream `stdGaussian_pi_mvPolynomial_*_integrable` theorems referenced but not shown.
- Model correspondence (whether this captures the intended Wishart/Jin application) requires external validation.
