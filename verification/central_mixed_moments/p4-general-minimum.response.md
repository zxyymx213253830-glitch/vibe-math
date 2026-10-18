# P4 Direct Mathematical Issues

## 1. Normalizing Ratio: Inverted Density Constant

**File:** `CentralRectangularMinimumPolynomial.lean`, `centralWishartDensityConstant_eq_square_ratio`

The claimed identity is:
```
K(d,n) = K(0,n) * (M(0,n,d))⁻¹
```

But the actual Wishart normalization requires $K(d,n) = K(0,n) / M(0,n,d)$ where $M(0,n,d) = \prod_{j=0}^{n-1} \frac{(j+d)!}{j!}$ is the **determinant bias ratio** $\mathbb{E}[\det(W)^d]$ under the square ($d=0$) law. The Lean statement writes this as multiplication by the inverse, which is algebraically equivalent only if $M(0,n,d) \neq 0$. The code invokes `(centralDeterminantPowerMoment_pos 0 n d).ne'` to justify this, but **the positivity proof itself depends on the normalizing constant being correctly defined**. This is circular: you need the correct $K(d,n)/K(0,n)$ ratio to prove the moment is positive, but you're using the moment's positivity to define the ratio.

**Severity:** Foundational. If `centralDeterminantPowerMoment` is defined via the $d$-parameterized density rather than computed explicitly as $\prod_{j=0}^{n-1}(j+d)!/j!$, the inversion is unjustified.

---

## 2. Gram Conjugate Order: `inl`/`inr` Swap in Polynomial Variables

**File:** `GramDeterminantPolynomial.lean`, `gramEntryPolynomial`

```lean
def gramEntryPolynomial (m n : ℕ) : Matrix (Fin n) (Fin n) (ComplexMatrixPolynomial m n) :=
  fun i j => ∑ k, MvPolynomial.X (Sum.inr (k,i)) * MvPolynomial.X (Sum.inl (k,j))
```

The type `ComplexMatrixPolynomial m n` is `MvPolynomial ((Fin m × Fin n) ⊕ (Fin m × Fin n)) ℂ`. By convention in `GaussianMatrixPolynomialLaw`, `Sum.inl` indexes $z_{ki}$ and `Sum.inr` indexes $\bar{z}_{ki}$. The Gram matrix entry $(Z^* Z)_{ij} = \sum_k \bar{z}_{ki} z_{kj}$ should therefore be:

$$\sum_k X(\text{inr}(k,i)) \cdot X(\text{inl}(k,j))$$

This matches the code. However, the evaluation theorem `eval_gramEntryPolynomial` then asserts this equals `complexSampleGram z i j`, which is defined via `complexGram` using `conjTranspose`. The issue is that **`MvPolynomial.eval` with `Sum.elim f g` applies `f` to `inl` and `g` to `inr`**, so:

```lean
let e := MvPolynomial.eval (Sum.elim (complexMatrixEntries z) (fun i => star (complexMatrixEntries z i)))
```

maps `inl(k,j) ↦ z_{kj}` and `inr(k,i) ↦ \bar{z}_{ki}`. The product in the polynomial is `X(inr(k,i)) * X(inl(k,j))`, which evaluates to $\bar{z}_{ki} \cdot z_{kj}$. This is correct for $(Z^*Z)_{ij}$.

**But:** the `shiftedGramDeterminantPolynomial` adds `x • 1` **before** taking the determinant power. The scalar matrix `x • 1` lives in `ComplexMatrixPolynomial m n`, meaning it is `MvPolynomial.C (x : ℂ)` times the identity matrix over the polynomial ring. This is fine algebraically, but the determinant is computed **in the polynomial ring**, not after evaluation. The identity `e(P.det) = (e(P)).det` used in `eval_shiftedGramDeterminantPolynomial` via `e.map_det` requires that `e` is a ring homomorphism, which `MvPolynomial.eval` is. **No issue here** — this is mathematically sound.

**Verdict:** No bug in conjugate order. The concern is resolved; the `inl`/`inr` assignment is consistent.

---

## 3. Real vs Complex Determinant Powers: The `.re` Extraction

**File:** `CentralWishartPolynomialIntegral.lean`, `shiftedGramDeterminant_power_real`

The theorem claims: for $x \geq 0$ and $z$ any complex sample,
$$\left(\operatorname{Re}\det(Z^*Z + xI)\right)^d = \det(Z^*Z + xI)^d \quad \text{(as a complex number)}$$

The proof argues: $Z^*Z \succeq 0$ and $xI \succeq 0$, so $Z^*Z + xI \succeq 0$, hence its determinant is real and nonneg. Therefore $\det(\cdot)^d$ is already real, and taking `.re` before or after the power gives the same result.

**Mathematical issue:** The statement `(((complexSampleGram z+(x : ℂ) • 1).det.re^d : ℝ) : ℂ) = (complexSampleGram z+(x : ℂ) • 1).det^d` is asserting equality **in ℂ**. The LHS coerces the real power back to ℂ. This is valid only because the RHS is proven to have zero imaginary part. The proof uses `Complex.nonneg_iff.mp hA.det_nonneg` which extracts `0 ≤ det.re ∧ det.im = 0`. 

**This is correct.** No issue.

---

## 4. Nonnegative-to-Bochner Conversion: Missing Measurability/AE Nonnegativity Justification

**File:** `CentralWishartPolynomialIntegral.lean`, `lintegral_actualCentralSquare_shiftedDeterminant_power`

The step:
```lean
rw [ofReal_integral_eq_lintegral_ofReal (integrable_actual_shiftedGramDeterminant_re_power n n d x hx)]
```

requires that the integrand `(A + x•1).det.re^d` is **nonneg a.e.** with respect to the Gaussian measure on samples. The proof supplies:
```lean
exact ae_of_all _ (fun z => pow_nonneg (Complex.nonneg_iff.mp ...).1 d)
```

This shows pointwise nonnegativity for **all** $z$, not merely almost everywhere. This is stronger than needed and is **correct**.

However, there is a subtler issue: `ofReal_integral_eq_lintegral_ofReal` converts a **Bochner integral** to a **Lebesgue lintegral**. This requires:
1. The function is Bochner integrable (supplied by `integrable_actual_shiftedGramDeterminant_re_power`).
2. The function is nonneg a.e. (supplied).
3. The measure space is σ-finite (standard Gaussian on finite-dimensional space — OK).

**But:** the Bochner integrability proof `integrable_actual_shiftedGramDeterminant_re_power` proceeds by taking `.re` of the complex-valued integrability:
```lean
have h := (integrable_actual_shiftedGramDeterminant_power m n d x).re
```

Taking the real part of an integrable complex function yields an integrable real function. This is valid (`Integrable.re`). Then the `he` rewrite changes the integrand from `det.re^d` to `(det^d).re` pointwise. The rewritten function is indeed the real part of the original complex integrand. **Correct.**

**Verdict:** No issue in the Bochner conversion chain.

---

## 5. Strict Tail Complement: CDF via `1 - tail` Requires Total Measure 1

**File:** `CentralRectangularMinimumPolynomial.lean`, `actualCentralRectangular_minimum_CDF`

```lean
((stdGaussian ...){z | minimum z ≤ x}).toReal = 1 - exp(-nx) * polynomial
```

This uses:
```lean
rw [actualCentralGaussian_minimum_CDF_eq_one_sub_tail, ...]
```

The identity $\mathbb{P}(\min \leq x) = 1 - \mathbb{P}(\min > x)$ holds iff the total measure is 1. The standard Gaussian `stdGaussian` is a probability measure, so this is satisfied.

**However**, the `.toReal` coercion is applied to the **ENNReal** measure of the set `{z | min z ≤ x}`. For this to equal `1 - tail`, we need:
1. Both `{min ≤ x}` and `{min > x}` are measurable (they are, as preimages of Borel sets under a measurable function).
2. They partition the space (they do: complementary sets).
3. The tail value is ≤ 1 so that subtraction in ENNReal doesn't saturate at 0 incorrectly.

Point 3 is the critical check: the tail is `exp(-nx) * polynomial(x)`. For $x \geq 0$, is this guaranteed ≤ 1? The code proves nonnegativity of the polynomial but **does not prove the tail ≤ 1 anywhere in this file**. It relies on the imported `actualCentralGaussian_minimum_CDF_eq_one_sub_tail` to handle the ENNReal arithmetic. If that lemma internally proves `tail ≤ 1` or works directly with the complement identity in probability measures (bypassing ENNReal subtraction), then it's fine.

**Potential issue:** If `actualCentralGaussian_minimum_CDF_eq_one_sub_tail` is stated as a raw ENNReal identity `μ(Aᶜ) = 1 - μ(A)` without verifying `μ(A) ≤ 1`, it could produce junk when `μ(A) > 1` (which can't happen for a probability measure, but the type system doesn't know `stdGaussian` is a probability measure unless explicitly invoked).

**Severity:** Low-medium. Likely handled in the imported bridge lemma, but worth verifying that `stdGaussian` is registered as a probability measure in scope.

---

## 6. Square-Wishart Restriction: `m := n` Hardcoded

**File:** `CentralWishartPolynomialIntegral.lean`, all theorems

Every result in this file fixes `m = n` (square Wishart):
```lean
(stdGaussian (ComplexSample (m := n) (n := n)))
(complexWishart (m := n) (n := n))
```

The rectangular CDF in `CentralRectangularMinimumPolynomial.lean` then handles general `d + n` rows by factoring through the square case via the density constant ratio. This factorization is:

$$\mathbb{E}_{d+n}[\det(W+xI)^d] = \frac{K(d,n)}{K(0,n)} \cdot \mathbb{E}_{n}[\det(W+xI)^d]$$

But this identity is **not generally true** for rectangular matrices. The left side integrates over $(d+n) \times n$ matrices while the right integrates over $n \times n$ matrices. The code derives this via `lintegral_complexWishart_eq_cone` which transports the rectangular integral to a square integral weighted by the cone indicator. This transport is valid **only if** the shifted determinant polynomial factors through the projection onto the square sub-block, which it does not in general — the determinant of a $(d+n)\times n$ Gram matrix involves all $d+n$ rows.

**This is the central mathematical gap.** The entire reduction from rectangular to square relies on `lintegral_complexWishart_eq_cone 0 n` applied to `fun A => (A + xI).det.re^d`. But `A` here ranges over $n \times n$ Hermitian matrices (the square Wishart support), while the original rectangular Gram matrix is $(d+n) \times n$. The cone integration lemma must account for the extra $d$ rows via the determinant bias, and the code asserts this through `centralWishartDensityConstant_eq_square_ratio`. 

**If** `lintegral_complexWishart_eq_cone` correctly marginalizes the rectangular Wishart to the square Wishart with the appropriate Radon-Nikodym derivative (the determinant power bias), then this is valid. But the polynomial `(A + xI).det^d` evaluated on the **square** matrix `A` is not the same as the determinant of the **rectangular** shifted Gram matrix unless the cone projection preserves the determinant structure, which requires proof.

**Severity:** High. This is the core rectangular-to-square reduction and needs explicit verification that the cone marginalization identity preserves the shifted determinant polynomial form.

---

## Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 1 | Normalizing ratio circularity | Foundational | Needs external factorial computation |
| 2 | Gram conjugate order | None | Verified correct |
| 3 | Real vs complex det powers | None | Verified correct |
| 4 | Bochner conversion | None | Verified correct |
| 5 | Tail complement in ENNReal | Low-Medium | Depends on imported lemma |
| 6 | Rectangular-to-square reduction | **High** | Core gap in polynomial transport |
