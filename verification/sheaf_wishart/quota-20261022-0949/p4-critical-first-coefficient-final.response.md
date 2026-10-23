# P4 Adversarial Review

## PositiveSpectrumFatouDivergence.lean

**1. `Real.log t` domain error in measurability proof.**
The term `(Real.log t)` appears in the construction of `hl` for arbitrary `t : ℝ`. When `t ≤ 0`, `Real.log t` returns junk (typically 0), but the mathematical definition of `positiveModeOffsetError` likely requires `t > 0`. The theorem statement quantifies over all `t : ℝ` in the `Tendsto` filter, yet the measurability proof silently uses an ill-defined expression for non-positive `t`. This is a **mathematical gap**: the proof body does not establish that the algebraic manipulation of `positiveModeOffsetError` into the displayed log-expression is valid for the entire domain claimed.

**2. Missing justification for Fatou application direction.**
`lintegral_liminf_le` gives an *upper* bound on the integral of the liminf. The conclusion `tendsto_of_le_liminf_of_limsup_le hFatou le_top` requires `hFatou` to serve as a lower bound on the liminf of integrals. But `lintegral_liminf_le` states `∫⁻ liminf u ≤ liminf ∫⁻ u`. After rewriting with `hlim` and `hInv`, we get `⊤ ≤ liminf ∫⁻ (...)`, which is correct. However, the final step uses `tendsto_of_le_liminf_of_limsup_le` which needs both bounds. Supplying `le_top` for the limsup half is trivially true but **logically incomplete**: that lemma yields convergence of the *sequence*, not divergence to `⊤`. To conclude `Tendsto ... atTop (𝓝 ⊤)`, one needs the liminf itself to equal `⊤`, not merely be bounded below by `⊤`. The `rw [hInv]` produces `⊤ ≤ liminf(...)`, forcing `liminf = ⊤`, but the cited lemma name suggests two-sided squeezing rather than the one-sided divergence argument actually needed. Verify the exact statement of `tendsto_of_le_liminf_of_limsup_le` handles the `⊤` case correctly or replace with the appropriate divergence lemma.

**3. Pointwise limit identification assumes uniform convergence structure.**
The step `hs' : Tendsto (fun t => t * ∑ i, positiveModeOffsetError ...) atTop (𝓝 (∑ i, (x i z)⁻¹))` uses `Finset.mul_sum` to push `t` inside. This requires each summand's scaled offset to converge to `(x i z)⁻¹`, which `positiveModeOffsetError_scaled_tendsto` supplies pointwise. No gap here given the imported dependency, but note: if any `x i z = 0`, then `(x i z)⁻¹ = 0` and the hypothesis `hx` only gives nonnegativity. The pointwise limit lemma must handle the zero-eigenvalue case; otherwise the AE set where convergence holds could exclude points where some `x i z = 0`.

## ActualCriticalFirstCoefficient.lean

**4. `criticalOffsetEq` requires full rank AE but applies pointwise.**
The identity `criticalOffsetEq` assumes `(complexSampleMatrix z * B + M).rank = m` as a pointwise hypothesis `hz`. In the main proof, it is applied after `filter_upwards [hRank]`, which is correct. However, `hRank` is derived from `actualCorrelatedRank_eq_generic_ae B M` combined with `hr`. The assumption `hr : m = (fromRows B M).rank` is deterministic, but `hRank` being AE depends on the measure-theoretic rank theorem holding for the specific Gaussian model. If `m > n` or `m > p + m` (the ambient row dimension), rank `m` is impossible. **No explicit dimensional feasibility constraint** (`m ≤ n`, `m ≤ p + m`) is stated; these are implicitly required for `hr` to be satisfiable.

**5. Index coercion `i.val + 1 = m` without bounds validation.**
The hypothesis `hi : i.val + 1 = m` with `i : Fin (Fintype.card (Fin n))` forces `m ≤ n`. Combined with `hm : 0 < m`, this implies `n ≥ 1`. These constraints are mathematically necessary but only appear encoded in the type/hypothesis interplay rather than as explicit preconditions. A reader cannot verify dimensional consistency without tracing `i`'s type through `Fin n`.

**6. Integrability subtraction chain.**
`hFI : Integrable F μ` is derived via `(hC.sub (integrable_const _)).sub hS).const_mul t`. This requires `actualCorrelatedMatrixLogDet B M t` minus `(m : ℝ) * Real.log t` minus `S` to remain integrable at each subtraction step. The first `.sub` is fine (constant is integrable on a probability space—**but `stdGaussian` on `ComplexSample` is not stated to be a probability measure in this file**; finite total mass is assumed from context). If `μ` has infinite total mass, `integrable_const` fails.
