# P4 Different-Model Review: Concrete Mathematical Analysis

## 1. Hermitian Trace Theorem — No Concrete Issue Found

The proof is standard deterministic linear algebra:
- Spectral decomposition `A = U*DU` via `hA.spectral_theorem`
- Unitary trace invariance: `trace(U*D²U) = trace(D²)`
- Real eigenvalues squared are real, so `.re` extracts cleanly
- `eigenvalues₀` vs `eigenvalues` reindexing via `Equiv.sum_comp` is valid for any finite type

No positivity, rank, or probability assumption is used. **No concrete issue.**

---

## 2. Polynomial Evaluation Homomorphism — No Concrete Issue Found

`eval_noncentralGramSquaredTracePolynomial` uses:
- `MvPolynomial.eval (Sum.elim ...)` which **is** a ring homomorphism (documented Mathlib signature)
- `AddMonoidHom.map_trace` and `Matrix.map_pow` for the polynomial-to-matrix transport
- Pointwise extensionality via `eval_noncentralGramEntryPolynomial`

This correctly distinguishes: `L` (integration) is linear; `eval` is a ring homomorphism. **No concrete issue.**

---

## 3. Integral Exchange — Potential Issue: `integral_re` Signature

```lean
have hr : (∫ z, f z.re ∂μ) = (∫ z, f z ∂μ).re := by simpa using! integral_re hi
```

**Concrete concern:** The theorem `integral_re` requires `Integrable f μ`. Here `hi` proves integrability of the *polynomial evaluation*, but the statement applies it to the `.re` projection inside the integral. This is mathematically correct (real part of an integrable complex function is integrable), but verify that `integral_re` in your Mathlib version accepts exactly `hi` without needing a separate `Integrable.re` wrapper. If the signature expects `Integrable (fun z => (f z).re) μ` rather than deriving it from `Integrable f μ`, this line fails at compile time.

**Severity:** Low — likely a `simpa`/`exact` fix if signatures align. Not a mathematical error.

---

## 4. Eigenvalue Sum Exchange — Concrete Issue: Empty Shape (m=0 or n=0)

```lean
rw [← integral_finsetSum _ (fun i _ => integrable_actualNoncentralEigenvalue_sq M i)]
```

When `m = 0` or `n = 0`:
- `Fin 0` is empty, so `∑ i : Fin 0, ...` = 0 (empty sum)
- `complexGram` becomes a 0×0 matrix with trace = 0
- `noncentralGramSquaredTracePolynomial M` evaluates to 0
- `complexGaussianPolynomialMoment` of the zero polynomial = 0

**Mathematically consistent**, but verify that `integrable_actualNoncentralEigenvalue_sq M i` is not invoked with an impossible index when the type is empty. In Lean, `fun i _ => ...` over `Fin 0` is vacuously satisfied, so this should pass. **No concrete issue** if `GaussianMatrixPolynomialLaw` handles zero polynomials (which it must, being stated for ANY polynomial).

---

## 5. Coefficient Transformation — Concrete Issue: Factorial Functional Form

You state:
> L(P) = finite SUM coeff(d) * PROD(if d(inl i) = d(inr i) then factorial(d(inl i)) else 0)

**Verification point:** For the squared-trace polynomial `((noncentralGramEntryPolynomial M)^2).trace`, the monomial support has degree ≤ 2 in each variable. When `d(inl i) ≠ d(inr i)` for any `i`, the product vanishes — this enforces that only "diagonal" moments survive Gaussian integration.

**Concrete check required:** Does `complexGaussianPolynomialMoment` expand via `GaussianMatrixPolynomialLaw` into exactly this factorial form, or does it use Wick's theorem/Isserlis' theorem internally? If the library's moment formula differs (e.g., includes cross-terms with covariance structure for non-standard Gaussians), the coefficient identity may not match your stated `PROD(...)` form.

Since you specify `stdGaussian` (identity covariance), Wick's theorem gives:
- `E[zᵢⱼ z̄ₖₗ] = δᵢₖδⱼₗ`
- Higher moments factor into pair products

For degree-2 polynomials, this yields exactly `factorial(1) = 1` per matched pair and `0` otherwise. **No concrete issue** for the squared-trace case specifically, but confirm that `GaussianMatrixPolynomialLaw` is proven for `stdGaussian` and not a general measure where the factorial form would be wrong.

---

## 6. Curvature Limit — No Concrete Issue Found

```lean
Tendsto (fun r => (r*T - ∫ actualLogDet ...) / r^2) (𝓝[>] 0) (𝓝 (moment.re / 2))
```

Given:
- Prior `actualNoncentralMatrixLogDet_low_scale_curvature` already establishes the limit shape
- `sum_integral_actualNoncentralEigenvalue_sq_eq_finite` substitutes the spectral sum with the polynomial moment
- `T = mn + ∑‖Mᵢⱼ‖²` matches the first-order expansion coefficient

The division by 2 comes from the Taylor expansion of `log det(I + rG) ≈ r·tr(G) - r²/2·tr(G²) + ...`, which is analytically correct. **No concrete issue.**

---

## Summary

| Component | Verdict |
|-----------|---------|
| Hermitian trace identity | No concrete issue |
| Polynomial eval homomorphism | No concrete issue |
| `integral_re` application | **Low-risk signature concern** — verify Mathlib exact type |
| Empty shape (m=0 ∨ n=0) | No concrete issue (vacuous sums) |
| Factorial coefficient form | No concrete issue for stdGaussian degree-2 |
| Curvature limit transport | No concrete issue |

**Overall:** No blocking mathematical error found. One minor formal verification item (`integral_re` signature alignment) should be confirmed against your Mathlib version. Human measure-theoretic review of the Gaussian model assumptions remains necessary as you noted.
