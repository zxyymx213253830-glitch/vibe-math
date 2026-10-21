# Minimal Route: Finite-N Planar Gaussian Polynomial Log-Integrability → Affine Matrix Compressed Determinants

## Stage 1: Universal Base Theorem (Current)

**What you have:**
For every `n : ℕ` and all `P : MvPolynomial (Fin n) ℂ` (including `P = 0`), under the convention `Real.log 0 = 0`:

```
∫⁻ x, |Real.log (eval P x)| ∂(stdGaussian (Fin n → ℂ)) < ∞
```

No nonzero premise. This is the correct universal statement because the zero-set of any polynomial has measure zero under the nondegenerate Gaussian, and the `log 0 = 0` convention handles the integrand on that null set.

---

## Stage 2: Transfer to `standardComplexPiLaw` via Scaling

**Construction:**
Given `P : MvPolynomial ι ℂ` with `ι` finite, let `e : ι ≃ Fin n` be an enumeration (via `Fintype.equivFin`). Define:

```
Q := MvPolynomial.rename e P    -- Q : MvPolynomial (Fin n) ℂ
```

Now construct the scaled polynomial. The key suggestion is right but needs precision:

```
scale := (√2)⁻¹
Q_scaled := Q.bind (fun i => C(scale) * X i)
```

**Semantic identity:**
```
eval Q_scaled z = eval Q (scale • z)
```
where `(scale • z)(i) = scale * z(i)` pointwise. This is a direct consequence of `bind` acting as the algebra homomorphism extending `X i ↦ C(scale) * X i`.

**Transfer step:**
```
∫⁻ z, |log (eval Q z)| ∂(standardComplexPiLaw (Fin n))
= ∫⁻ z, |log (eval Q_scaled ((√2) • z))| ∂(stdGaussian (Fin n → ℂ))
```

Wait—this direction is backwards. Let me state it correctly:

Since `standardComplexPiLaw ι = (stdGaussian ℂ).map (fun z => (√2)⁻¹ • z)` per coordinate, we have:

```
∫⁻ w, |log (eval P w)| ∂(standardComplexPiLaw ι)
= ∫⁻ z, |log (eval P ((√2)⁻¹ • z))| ∂(stdGaussian (ι → ℂ))
= ∫⁻ z, |log (eval P_scaled z)| ∂(stdGaussian (ι → ℂ))
```

where `P_scaled := P.bind (fun i => C((√2)⁻¹) * X i)`.

**This is finite by the base theorem applied to `P_scaled`** (after transporting through `e : ι ≃ Fin n`).

> **HUMAN REVIEW MARKER 1:** Verify that `MvPolynomial.bind` composed with scalar multiplication gives exactly the pointwise-scaled evaluation. The identity `eval (P.bind f) x = eval P (fun i => eval (f i) x)` must reduce to `eval P (scale • x)` when `f i = C(scale) * X i`. This is true by `eval_C_mul_X` but write out the one-liner explicitly.

---

## Stage 3: Arbitrary Finite Index Type via Enumeration

**Route:**
1. Given finite `ι`, obtain `e : ι ≃ Fin n` where `n = Fintype.card ι`.
2. Use `MvPolynomial.rename e : MvPolynomial ι ℂ →+* MvPolynomial (Fin n) ℂ`.
3. Apply base theorem to `rename e P_scaled`.
4. Transport back: `Measure.pi` over `ι` equals `Measure.map (fun x => x ∘ e) (Measure.pi over Fin n)` by reindexing.

**Key lemma needed:**
```
standardComplexPiLaw ι = (standardComplexPiLaw (Fin n)).map (fun f => f ∘ e)
```
This follows from `Measure.pi_map_pi` since each factor map is identical (`(√2)⁻¹ •`) and the product structure is preserved under bijection of index types.

> **HUMAN REVIEW MARKER 2:** `Measure.pi_map_pi` requires sigma-finiteness of each factor. `standardComplexScalarLaw` is sigma-finite (it's a probability measure). Confirm the Lean statement accepts the `fun _ => standardComplexScalarLaw` constant family form directly, or if you need to spell out the `MeasurableSpace` instances on each factor.

---

## Stage 4: Physical Matrix Entries via `complexMatrixEntries_law`

**Given:**
```
complexMatrixEntries_law m p :
  (stdGaussian (ComplexSample (m × p))).map complexMatrixEntries 
  = standardComplexPiLaw (Fin m × Fin p)
```

Here `ComplexSample(m,p)` is the real vector space `Fin m → Fin p → ℝ × ℝ` (or equivalent), and `complexMatrixEntries` extracts the `m × p` complex matrix.

**Transfer for arbitrary polynomial in entry variables:**
Let `R : MvPolynomial (Fin m × Fin p) ℂ` be any polynomial in the *physical complex matrix entries*. Then:

```
∫⁻ M, |log (eval R (complexMatrixEntries M))| ∂(stdGaussian (ComplexSample (m × p)))
= ∫⁻ Z, |log (eval R Z)| ∂(standardComplexPiLaw (Fin m × Fin p))
< ∞
```

The equality is exactly `Measure.map_apply` + change of variables. The finiteness is Stage 2-3 with `ι = Fin m × Fin p`.

> **HUMAN REVIEW MARKER 3 (CRITICAL SEMANTIC TRAP):** Do NOT conflate `R` (a polynomial in the `m*p` complex entry variables `Z_{ij}`) with `sampleEval` (a polynomial in the `2*m*p` real coordinate variables of `ComplexSample`). The map `complexMatrixEntries` is `ℝ`-linear but not `ℂ`-linear in the naive variable ordering. If you have a polynomial expressed in real/imaginary parts `(Re Z_{ij}, Im Z_{ij})`, you must first rewrite it as a polynomial in `(Z_{ij}, Z̄_{ij})` or directly in `Z_{ij}` if it's holomorphic. For the log-integrability bound, you only need `R` as a polynomial in the complex variables—the base theorem doesn't require holomorphy, just polynomial structure. But downstream (Stage 5), holomorphy matters.

---

## Stage 5: Affine Physical Gaussian Matrix Compressed Determinants

**Setup:**
Let `A : Matrix (Fin q) (Fin m) ℂ` and `B : Matrix (Fin q) (Fin p) ℂ` be fixed deterministic matrices. Let `M ~ stdGaussian (ComplexSample (m × p))`. The compressed determinant is:

```
D(M) := det (A * M * B)    -- or more generally det(A*M + B) depending on "affine"
```

This is a polynomial in the entries of `M`. Specifically:

```
D = det_compressed_poly A B : MvPolynomial (Fin m × Fin p) ℂ
```

constructed via the Leibniz formula applied to the `q × q` matrix whose `(i,j)` entry is `Σ_k,l A_{i,k} * X_{(k,l)} * B_{l,j}`.

**Integrability conclusion:**
```
∫⁻ M, |log |det (A * M * B)|| ∂(stdGaussian (ComplexSample (m × p))) < ∞
```

follows immediately from Stage 4 by taking `R = det_compressed_poly A B`, **provided `R ≠ 0`**.

> **HUMAN REVIEW MARKER 4:** When is `det_compressed_poly A B = 0`? Precisely when the linear map `M ↦ A*M*B` has rank `< q` for all `M`, i.e., when `rank(A) < q` or `rank(B) < q`. If `A` or `B` drops rank, the polynomial is identically zero and `log |0| = 0` by convention—still integrable, but vacuously. For the meaningful statement (controlling negative log near zeros of a *nonzero* polynomial), assert `rank A = q` and `rank B = q` (which forces `q ≤ min(m,p)`). The base theorem covers `R = 0` trivially; the content is for `R ≠ 0`.

**Why this works without pseudo-tools:**
- No API hypothesis about "determinant of random matrix" is needed.
- `det (A*M*B)` is literally a polynomial in the entries of `M` with coefficients determined by `A, B`.
- You construct `det_compressed_poly` by composing `MvPolynomial.monomial` / `C` / `X` operations following the Leibniz expansion.
- Integrability is inherited from the universal polynomial result.

---

## Semantic Traps Summary

| # | Trap | Avoidance |
|---|------|-----------|
| 1 | Using `sampleEval` (real-coordinate polynomial) as if it were a polynomial in complex entries | Always pass through `complexMatrixEntries_law` to get `standardComplexPiLaw`, then apply polynomial in `Z_{ij}` variables |
| 2 | Assuming `bind (fun i => C(c) * X i)` scales evaluation without proof | Prove `eval (P.bind f) x = eval P (λi, eval (f i) x)` reduces to `c • x` for `f i = C(c)*X i` |
| 3 | Forgetting that `Measure.pi_map_pi` needs sigma-finiteness | Each factor is a probability measure; cite this explicitly |
| 4 | Treating `det(A*M*B)` as holomorphic in `M` when analyzing singular values | The determinant polynomial is holomorphic in entries; singular values are not. Keep Stage 5 at the polynomial level |
| 5 | Conflating `Fin m × Fin p` indexing with `ComplexSample` real coordinates | Use `complexMatrixEntries_law` as the bridge; never skip it |

---

## Next Target Boundary (PseudoDet Spectral Comparison) — NOT proved here

**Statement to isolate for future work:**
Given `q ≤ min(m, p)` and fixed matrices such that `rank [B; M] = q` a.e. (generic rank condition), compare:

```
-log |det_q-minor(A*M*B)|   vs.   -Σ_{i=1}^q log σ_i(A*M*B)
```

where `σ_i` are the positive singular values.

**What is NOT yet established:**
- That `q = min(m, rank(stacked [B; M]))` holds almost everywhere (you said "generic rank AE"—this needs a dimension argument or citation)
- Any spectrum inequality bounding the ratio or difference of these two quantities
- That the `q`-minor determinant controls the product of top `q` singular values from below in a log-integrable way

**Do not assume these.** The route above gives you L1 bounds for `-log |det(polynomial)|` for any fixed polynomial (including minors). Transferring that to singular value products requires the spectral comparison as a separate analytic input.

---

## One-Hour Execution Checklist

1. **[10 min]** Write `P_scaled := P.bind (fun i => C((√2)⁻¹) * X i)` and prove `eval P_scaled z = eval P ((√2)⁻¹ • z)`.
2. **[10 min]** Invoke base theorem to get `logL1` under `standardComplexPiLaw (Fin n)`.
3. **[10 min]** State and prove `standardComplexPiLaw ι ≅ standardComplexPiLaw (Fin n)` via `equivFin` + `Measure.pi_map_pi` reindexing.
4. **[10 min]** Apply `complexMatrixEntries_law` to push forward to `stdGaussian (ComplexSample (m×p))`.
5. **[15 min]** Construct `det_compressed_poly A B` explicitly as an `MvPolynomial`; prove `eval (det_compressed_poly A B) (entries M) = det (A*M*B)`.
6. **[5 min]** Conclude integrability; mark the four HUMAN REVIEW markers for sign-off.
