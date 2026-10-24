# P1 Bounded Route Comparison

## Route A: Andreief on Restricted Volume

**New lemmas (minimal list):**
1. Export `Complex.partialGamma` real-polynomial interface via `partialGamma_nat_eq_realLower` replica (no old proof change).
2. Ordered-half lemma: for SFinite μ, measurable H symmetric with H(x,x)=0, ∫_{y<x} H d(μ⊗μ) = (1/2)∫ H d(μ⊗μ).
3. Restriction compatibility: `volume.restrict (Ioc 0 x)` is SFinite; endpoint {x} is null.
4. Moment-matrix identification: f_i(y)=y^i·exp(-y/2) yields lower-incomplete-Gamma entries under restriction.

**Measurability/conditions:** Pairwise integrability of f_i·g_j under restricted measure; polynomial·exponential is measurable; finite integral guaranteed on bounded interval Ioc 0 x. Endpoint x contributes null set. Diagonal u=v has measure zero under product, satisfying H(u,u)=0 requirement.

**Failure modes:** ENNReal determinant equality lives in [0,∞]; extracting signed real determinant norm requires proving the matrix is positive-semidefinite or controlling sign explicitly. The ordered-half lemma produces ENNReal division by 2; coercing to ℝ demands finiteness. Risk: circularly deriving actual law from candidate formula if moment-matrix identification implicitly assumes the target CDF.

## Route B: Direct Tonelli Triangular Integration

**New lemmas (minimal list):**
1. Inner integral closed form: ∫_v^u (u-v)²·exp(-(u+v)) dv = (u²-2u+2)e^{-u} - 2e^{-2u} (elementary calculus).
2. Outer integral: ∫_0^x [(u²-2u+2)e^{-u} - 2e^{-2u}] du = 1-(x²+2)e^{-x}+e^{-2x}.
3. Tonelli applicability: integrand nonneg, measurable on triangular region {(u,v): 0<v<u<x}.

**Measurability/conditions:** Integrand is continuous on compact triangle, hence measurable and finite. No endpoint pathology: v=0 included, u=x included, diagonal v=u has planar measure zero. Nonnegativity is immediate from (u-v)²≥0 and exp>0.

**Failure modes:** Fewer—purely computational. Risk: arithmetic error in polynomial-exponential antiderivative. No ENNReal-to-real coercion needed since integrand is manifestly nonneg real-valued throughout.

## Comparison

| Criterion | Route A (Andreief) | Route B (Tonelli) |
|-----------|-------------------|-------------------|
| New lemma count | ~4 (including export) | ~3 (computational) |
| Measurability burden | High (SFinite, pairwise integrable, ENNReal) | Low (continuous on compact) |
| Endpoint/null-set | Ioc boundary, diagonal null | Triangle boundary, diagonal null (trivial) |
| ENNReal→ℝ risk | Determinant norm extraction, sign control | None (nonneg real throughout) |
| Circularity risk | Moderate (moment matrix may encode target) | Low (direct verification) |

## Critical Safeguards

**Avoiding positivity assumptions:** Never assert det(moment_matrix)≥0 without proof. Route B sidesteps this entirely—integrand (u-v)²·exp(-(u+v)) is manifestly ≥0. Route A requires proving the Gamma matrix determinant is nonneg before taking real norm; use existing T2(s,t,L)=(2,2,0) structure which already encodes this.

**Avoiding circularity:** Do not derive actual joint law from expected CDF formula. The law `withDensity exp(-(u+v))·(u-v)²` is already Lean-proved. Both routes compute its CDF; neither should assume the answer. Verify inner integral (Route B) or moment entries (Route A) against definitions, not against target 1-(x²+2)e^{-x}+e^{-2x}.

**Numeric vs. proof:** Floating-point evaluation of crossing point F_min-F_max=(x²+2)e^{-x}-2e^{-2x}≠0 identifies candidate x₀; formal proof requires IVT on the continuous difference, not rounded comparisons.

**Event distinctions:** Max CDF event uses weak inequality (≤x), giving right-continuous CDF. T3 crossing concerns strict sign change of F_min-F_max; at crossing point itself, equality holds but this single point has measure zero.

**Human review required:** Measure-theoretic setup (Fubini/Tonelli hypotheses, sigma-finiteness) and paper-level sanity checks remain human obligations. Codex executes; human validates modeling choices.
