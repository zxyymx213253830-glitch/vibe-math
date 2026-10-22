## P4 Adversarial Review: `CanonicalShearFactorMoments.lean`

**1. Critical Mathematical Gap: Type Mismatch in `MemLp` Application**

The theorem's conclusion asserts `Integrable (fun z => (1 + ‖...‖)^q) μ`, which is integration against the measure `μ`. However, `hG.integrable_norm_rpow'` is applied to `hG : MemLp (...) r μ` where `r := ENNReal.ofReal q`. The `MemLp` predicate and its associated integrability results operate on the **norm** of a function into a normed space. Specifically, `hG` establishes that the real-valued function `z ↦ 1 + ‖(Matrix.toEuclideanLin (...)).toContinuousLinearMap‖` is in $L^r(\mu)$.

The gap: `integrable_norm_rpow'` yields `Integrable (fun z => ‖(1 + ‖...‖)‖^q) μ` (or equivalent formulation depending on exact Mathlib signature). Since the codomain is `ℝ` and the expression `1 + ‖...‖` is nonnegative, this reduces to `Integrable (fun z => (1 + ‖...‖)^q) μ`. **This step is actually correct**, but the proof obscures why: it relies on the fact that for nonneg reals, the outer norm `‖·‖` in the `MemLp` definition collapses to the identity. The final `convert` with `Real.norm_of_nonneg` patches this, but the intermediate `hG` uses `.add` on a constant `1 : ℝ` against `hW.norm` — this requires that `hW.norm` produces a `MemLp` statement about the **real-valued** norm function, and that adding a constant preserves `MemLp`. This is valid only if the constant function is itself `MemLp`, which requires **finite measure** or bounded domain. The measure here is `stdGaussian` on a finite-dimensional space (total mass 1), so this holds, but **the finiteness of the Gaussian measure is never explicitly invoked**. If `ComplexSample` were infinite-dimensional or the measure were not finite, `memLp_const` would fail.

**2. Semantic Gap: `leftOperatorLinear` Codomain vs. `F M` Addition**

`leftOperatorLinear Q` maps into `EuclideanSpace ℂ (Fin b) →L[ℂ] EuclideanSpace ℂ (Fin c)`. In `hW`, the proof converts via:
```
(Matrix.toEuclideanLin (Q*(complexSampleMatrix z+M))).toContinuousLinearMap = ... + F M
```
But `F M` has type `EuclideanSpace ℂ (Fin b) →L[ℂ] EuclideanSpace ℂ (Fin c)` while `F.restrictScalars ℝ` changes the scalar field. The addition `hL.add (memLp_const (F M))` requires `F M` to live in the **same** normed space as the output of `L`. After `restrictScalars ℝ` and composition, `L` maps into continuous linear maps over `ℝ`, but `F M` is defined via `leftOperatorLinear` over `ℂ`. The `convert` succeeds syntactically because `simp [Matrix.mul_add]` resolves the algebraic equality, but the **normed space structure** used for `memLp_const (F M)` must match exactly. If `restrictScalars` changes the norm (it shouldn't for finite-dimensions, but this is a semantic dependency), the `MemLp` statement would reference different norms.

**3. Missing Justification: `IsGaussian.memLp_id` Applicability**

`hraw` invokes `IsGaussian.memLp_id μ r (by simp [r])`. This requires `μ` to satisfy the `IsGaussian` predicate. The docstring flags "[需人工审查] Inherited Gaussian measure/model" — the proof **assumes** `stdGaussian (ComplexSample ...)` is recognized as Gaussian by Mathlib's Fernique theorem infrastructure. This is an API-level dependency, not a mathematical gap per se, but if `ComplexSample` carries a non-standard Borel structure or if `stdGaussian` constructs a product measure not flagged `IsGaussian`, the invocation fails silently at the semantic level.

**Summary:** One actual gap (finite measure for `memLp_const` left implicit), one fragile type-coercion seam (`restrictScalars` + `toContinuousLinearMap` norm compatibility), one flagged API dependency.
