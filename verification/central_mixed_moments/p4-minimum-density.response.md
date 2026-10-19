# Human Measure/Model Review: P4 Boundary, Truncation, and Interpretation Audit

## 1. Boundary x=0 and Negative Axis Behavior

**MeasureFromPositivePrimitive.lean**
- `hCDF` defines the CDF as exactly 0 for x < 0. This is a hard truncation, not an analytic continuation. No fictitious extension.
- `G 0 = 0` (h0) forces no atom at 0. Since μ(Iic 0) = G(0) = 0, we get μ({0}) = 0. The density value h(0) at the single boundary point is measure-theoretically irrelevant (a.e. equivalence).
- For x < 0, the proof uses `Ioc 0 x = ∅` when x < 0, giving lintegral = 0, matching the CDF. Correct.
- **No assumed analytic CDF**: the piecewise definition is explicit via `ite`. Global G is NOT claimed to be the CDF on the negative axis; only its restriction to [0,∞) matters.

**CentralMinimumActualDensity.lean**
- `centralMinimumCDFContinuation_zero` proves G(0) = 0 algebraically from polynomial evaluation (P(0) = M, exp(0) = 1, so 1 - M/M = 0). Consistent.
- `actualCentralMinimum_cdf_eq_piecewise_continuation` inherits the hard truncation at 0 from the independently proved actual matrix CDF.

## 2. ofReal Truncation and Non-negativity

- `ENNReal.ofReal (h x)` truncates negative values to 0. However, `centralMinimumPDFCore_nonneg` (proved via `primitive_derivative_nonneg_of_cdf`) guarantees h(x) ≥ 0 for all x > 0 using monotonicity of the actual CDF. Thus on Ioi 0, ofReal acts as the identity embedding into ENNReal. No silent mass loss.
- On x ≤ 0, the indicator kills the density, so ofReal behavior there is irrelevant.
- **h ≥ 0 is a theorem**, not an axiom. It follows from CDF monotonicity + local derivative equality on (0,∞).

## 3. Finite Integral Conversion (FTC)

- `intervalIntegral.integral_eq_sub_of_hasDerivAt` requires continuity of h (given by `continuous_centralMinimumPDFCore`) and pointwise derivative everywhere (given by `hasDerivAt_centralMinimumCDFContinuation`). Both are proved.
- `IntervalIntegrable` follows from continuity on compact [0,x].
- `ofReal_integral_eq_lintegral_ofReal` conversion requires interval integrability of |h| (guaranteed by continuity) and a.e. non-negativity on the domain (guaranteed by hnn on Ioc 0 x).
- No improper integral issues: for any finite x ≥ 0, the interval [0,x] is compact.

## 4. Actual Gaussian Map Measurability

- `centralGaussianSampleMinimum` measurability is inherited from `measurable_centralGaussianSampleMinimum` (used in CentralMinimumPDF.lean for `aemeasurable`).
- Pushforward measure `.map` is well-defined given this measurability.
- stdGaussian on ComplexSample is a Borel probability measure on a finite-dimensional real vector space. No σ-finiteness or quasi-Borel pathologies.

## 5. Variance and Raw Gram Interpretation

- **Variance-one complex entries**: stdGaussian implies E[|z|²] = 1 per complex entry (variance 1/2 per real/imag component, total 1). This matches the N = n+1 scaling in the exponential exp(-Nx).
- **Raw Gram (not normalized)**: The matrix is X†X where X is d×(n+1), not X†X/(n+1). The minimum eigenvalue λ_min scales as O(1) with this convention, consistent with the CDF form 1 - exp(-Nx)·P(x)/M.
- **N = n+1 > 0**: Guaranteed by Nat.succ_pos n. No division by zero, no degenerate empty matrix.
- **m = d + (n+1)**: Rectangular matrix with m ≥ n+1 (since d ≥ 0). Ensures full column rank a.s., so λ_min > 0 a.s. (consistent with no atom at 0).

## 6. One-Dimensional Marginal vs G2 Joint Density

- Explicitly documented: this is the law of the scalar minimum eigenvalue, NOT the joint spectral density of all eigenvalues.
- No Jacobian prefactor confusion: the density arises purely from differentiating the marginal CDF, not from integrating out a joint density over a Weyl chamber.
- Polynomial P and factorial M come from the determinantal/power-moment structure, not from a Selberg-type integral normalization.

## 7. Measure Extensionality (ext_of_Iic)

- Two measures agreeing on all Iic x sets are equal. Applied correctly.
- Probability measure normalization (lintegral = 1) is a consequence, not an assumption—verified in `lintegral_actualCentralMinimumDensity` via measure_univ.

## 8. No Fictitious Claims Detected

- No "uniform noncentral" assertion anywhere.
- No classical prefactor identity invoked—the density formula is derived purely from FTC on the proved CDF.
- No target PDF assumed—the HasPDF instance is constructed *after* proving the measure equality, not before.

---

## Summary Verdict

| Aspect | Status |
|--------|--------|
| CDF truncation at 0 | Correct, explicit ite |
| Atom at 0 | Excluded by G(0)=0 |
| ofReal safety | Protected by proved non-negativity |
| FTC applicability | Continuous h + pointwise HasDerivAt |
| Gaussian measurability | Inherited, standard Borel |
| Variance/Gram scaling | Consistent with N=n+1, raw Gram |
| Marginal vs joint | Correctly scoped |
| Analytic continuation fiction | Absent |
| Axiom count | Standard Mathlib (choice, classical, funext) |

**Conclusion**: The reconstruction is measure-theoretically sound. The density is a theorem-level consequence of the independently proved CDF, not a modeling assumption. Boundary/pathology concerns are handled by explicit proofs (non-negativity, continuity, G(0)=0). No review-blocking issues identified under FinalCodex12 kernelPASS standard3axioms.
