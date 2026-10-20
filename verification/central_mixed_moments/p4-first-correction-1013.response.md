# P4 Adversarial Review: Issues Only

## NoiselessRowFirstCorrection.lean

**1. Potential type mismatch in `rowLogDet_offset_error_identity` application (line 58-59)**

The theorem `rowLogDet_first_correction_bounds` takes `X : Matrix (Fin m) (Fin n) ℂ` but applies `complexGram Xᴴ`. The identity `rowLogDet_offset_error_identity X hm δ r hδ hfloor hr` is rewritten into the goal. If that identity was proved for `complexGram X` rather than `complexGram Xᴴ`, or with different dimension parameters, the `rw [hi, rowLogDet_offset_error_identity ...]` step silently fails or produces a type-incorrect intermediate. The reviewer cannot verify the exact statement of the imported lemma; this is a scope/correspondence risk flagged as [需人工审查].

**2. Eigenvalue indexing domain assumption (lines 47-49)**

`hf` quantifies over `i : Fin (Fintype.card (Fin m))`, which reduces to `Fin m`. This relies on `complexGram Xᴴ` being exactly `m × m` and having exactly `m` ordered eigenvalues. If `gramSmallestValue_le_orderedEigenvalue` was proved under an additional rank or positivity hypothesis not carried by `hm : 0 < m` alone, then `hf` has a hidden precondition. Zero-dimensional intentionality does not apply here since `hm : 0 < m`, but the case where eigenvalues are padded or truncated in the imported definition is not checked locally.

**3. Upper bound denominator uses `δ` rather than spectrum-dependent values (line 40-42)**

The step `one_div_le_one_div_of_le ... (pow_le_pow_left₀ hδ.le (hl i) 2)` replaces each `(l i)^2` with `δ^2` in the denominator. This is valid only if `δ ≤ l i` implies `δ^2 ≤ (l i)^2`, which requires `0 ≤ δ`. That holds via `hδ : 0 < δ`. No issue here upon close inspection, but the tightness claim in the module docstring ("global half-quadratic bound") could be misleading: the bound is uniform across the spectrum using the floor, not per-eigenvalue.

---

## CorrelatedNoiselessFirstCorrection.lean

**4. Integrability subtraction order assumes both terms finite (lines 36-38)**

`hE : Integrable E (stdGaussian _) := (hC.sub (integrable_const _)).sub hL` requires that `hC.sub (integrable_const _)` and `hL` are each integrable. `hL` comes from `integrable_actualCorrelatedRowLogDet_of_noiseless_surjective B M hm hs`, which depends on the surjectivity hypothesis `hs`. If `hs` fails or is mis-stated relative to the actual model correspondence (the `M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)` range condition), then `hL` is unsupported. The [需人工审查] tag acknowledges this, but the proof does not guard against silent vacuity—if `hs` is uninhabited, the theorem is vacuously true while appearing substantive.

**5. Pointwise bound `hb` applied inside integral without measurability discharge (lines 49-53)**

`hb (z : ComplexSample ...)` invokes `rowLogDet_first_correction_bounds (complexSampleMatrix z * B + M) ...`. This requires that for every `z`, the matrix `complexSampleMatrix z * B + M` satisfies the floor condition `hfloor (complexSampleMatrix z)`. The `hfloor` comes from `correlated_rowGram_uniform_floor`, which gives a *uniform* `δ` for all `z`. However, the `simpa only [...] using` rewrite unfolds definitions and must produce exactly the syntactic form expected by `rowLogDet_first_correction_bounds`. If `actualCorrelatedRowInverseTracePow` or `actualCorrelatedMatrixLogDet` unfold to expressions that differ by associativity, conjugation order, or coercion from the noiseless theorem's expectation, the `simpa` closes the goal only by accident or leaves a hidden kernel-level mismatch. This is a model correspondence issue within the [需人工审查] scope.

**6. `integral_offset_remainder_bounds` linearity/squeeze preconditions (lines 55-58)**

The application passes `(hE.const_mul r)` as the integrability witness for `fun z => r * E z`. This is correct only if `r` is a fixed real scalar at that point in the proof—but `r` is universally quantified in the goal (`∀ r : ℝ, 0 < r → ...`). The `let E := ...` and `hE` depend on `r`, so `hE.const_mul r` is well-typed for each fixed `r`. No logical error, but the dependency structure means the integrability proof is re-done for each `r`, and the uniform `δ` from `correlated_rowGram_uniform_floor` must not itself depend on `r`. Checking the type of `correlated_rowGram_uniform_floor`: it returns `⟨δ, hδ, hfloor⟩` before `r` is introduced, so this is safe.

**7. Tendsto proof uses `squeeze_zero'` with asymmetric bounds (lines 72-78)**

`squeeze_zero'` requires the lower bound to tend to 0 and the upper bound to tend to 0, squeezing the middle. The lower bound `(hb r hr).1` gives `0 ≤ L - r * offset`, and the upper bound `(hb r hr).2` gives `L - r * offset ≤ m / (2*r*δ^2)`. The squeeze target is `hK : Tendsto (fun r => (m/(2*δ^2))/r) atTop (𝓝 0)`. This is arithmetically correct. However, `squeeze_zero'` also requires the *lower* bounding function to converge to 0; here the lower bound is the constant function 0, which trivially tends to 0. No issue, but the Lean invocation `apply squeeze_zero' ?_ ?_ hK` leaves two goals open that are closed by `filter_upwards`. If either filter direction were reversed (e.g., using `atBot` instead of `atTop`), this would fail silently. The `eventually_gt_atTop (0:ℝ)` is correct for `r → +∞`.

**8. Final simplification `sub_sub_cancel` (line 79)**

`simpa only [sub_sub_cancel, sub_zero] using hs` rewrites `L - (L - r * offset)` to `r * offset`. This is purely algebraic and correct, but note that the limit statement concludes `Tendsto (fun r => r * actualCorrelatedExpectedRowOffsetError B M r) atTop (𝓝 L)`, meaning the first correction *times r* converges to the inverse-trace integral. The theorem name says "tendsto" without clarifying that it is `r * offset → L`, not `offset → L/r`. Not an error, but a naming/scope mismatch risk for downstream consumers.

---

## Cross-module issues

**9. Dimension consistency for `B : p × n`, `M : m × n`, `sourceZ : m × p`**

The module header states these dimensions. In `actualCorrelatedExpectedRowOffsetError`, the sample space is `ComplexSample (m := m) (n := p)`, so `z` is `m × p`. Then `complexSampleMatrix z * B` is `(m × p) * (p × n) = m × n`, matching `M`. This is consistent. However, `complexGram` of an `m × n` matrix yields `m × m` (if defined as `X * Xᴴ`) or `n × n` (if `Xᴴ * X`). The noiseless theorem uses `complexGram Xᴴ` where `X : m × n`, so `Xᴴ : n × m` and `complexGram Xᴴ` should be `n × n`—but the eigenvalue sum runs over `Fin m` (via `Fintype.card (Fin m)`). This suggests `complexGram` is defined as `Xᴴ * X` yielding `n × n` only when `n = m`, or the imported definition uses the other convention. **This is the most critical hidden assumption**: if `complexGram A = A * Aᴴ` vs `Aᴴ * A` differs between the imported files, the trace/eigenvalue correspondence breaks. Flagged for [需人工审查].

**10. CN1 source coordinate normalization**

The header states "CN1 source uses two standard real coordinates divided by sqrt2." This normalization factor must propagate through `stdGaussian`, `complexSampleMatrix`, and into the log-det expressions. If any imported lemma was proved under a different normalization (e.g., variance 1 per complex entry rather than variance 1/2 per real component), the constant `m / (2*r*δ^2)` would be off by a factor of 2. No local check verifies this; it is entirely delegated to imports.

---

## Summary of issues requiring attention

| # | File | Severity | Nature |
|---|------|----------|--------|
| 1 | NoiselessRow | Medium | Lemma statement/argument order mismatch risk |
| 4 | Correlated | High | Surjectivity hypothesis `hs` may be vacuous or mis-scoped |
| 5 | Correlated | High | Definition unfolding across model correspondence boundary |
| 9 | Cross-module | Critical | `complexGram` convention (XXᴴ vs XᴴX) determines trace dimension match |
| 10 | Cross-module | Medium | √2 normalization consistency delegated entirely to imports |

Items 4, 5, 9 fall within the declared [需人工审查] scope. Items 1 and 10 are structural risks not explicitly covered by that tag.
