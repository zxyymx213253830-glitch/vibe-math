# Locked target statements

Revision 2 corrects a named-argument lexer truncation. Full literal Lean targets are unchanged. Original lock archived; both checks rerun. Never auto-relock changed mathematical targets.

## JinWishart.stdGaussian_complex_closedBall_le_radius_sq_half

```lean
(μ : ℂ) (R : ℝ) (hR : 0≤R) : (stdGaussian ℂ).real (Metric.closedBall μ R) ≤ R^2/2
```

## JinWishart.actual_noncentralScalarCDF_le_threshold_uniform_mean

```lean
(M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) (hx : 0≤x) : cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x ≤ x
```
