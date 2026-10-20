# P4 Adversarial Final-Source Review

## ProbabilityNegativeLogBounds.lean

**1. Missing measurability of `{a | f a ≤ x}` in `negativeLog_probabilityTail_le`.**
The hypothesis `hsmall` quantifies over `μ.real {a | f a ≤ x}`, but the theorem never assumes `Measurable f`. For an arbitrary function `f : α → ℝ`, the sublevel set `{a | f a ≤ x}` need not be measurable, so `μ.real` applied to it is ill-defined (or silently equals zero via outer-measure totalization, depending on your `measureReal_def`). The second theorem fixes this by passing `hf : Measurable f`, but the first theorem does not require it. Either add `(hf : Measurable f)` to `negativeLog_probabilityTail_le`, or confirm that your `μ.real` wrapper is explicitly defined for all sets and you intend the bound to trivialize for non-measurable `f`.

**2. `measurable_const.max (hf.log.neg)` relies on totalized `Real.log 0 = 0`.**
You flag this correctly. The composition `hf.log` requires that `Real.log` is Borel-measurable as a total function `ℝ → ℝ`. With `Real.log 0 = 0`, this holds, but it is worth noting that `hf.log` uses the instance `Measurable Real.log`, which depends on the specific Mathlib version's treatment of totalized functions. Not a bug given your premises, but a fragile dependency.

**3. `ENNReal.ofReal_toReal (measure_ne_top _ _)` in `heq`.**
This step converts between `∫⁻` and `∫` via `lintegral_eq_lintegral_meas_le`. The identity `ENNReal.ofReal (μ.real s) = μ s` requires `μ s ≠ ⊤`. You discharge this with `measure_ne_top _ _`, which is correct for probability measures. No issue.

**4. Layer-cake direction.**
`lintegral_eq_lintegral_meas_le` gives `∫⁻ y, μ {a | Y a ≥ y}`. Your `probabilityTail` must therefore be defined as `μ.real {a | Y a ≥ t}` (upper tail), not the strict `> t` variant. If `probabilityTail` uses `> t`, the equality `heq` fails at atoms. Confirm the definition matches.

**5. `integral_mono_ae htail hmajor` type.**
Both `htail` and `hmajor` are `IntegrableOn` over `Ioi 0`. The conclusion integrates over `Ioi 0`. This is consistent provided `integral_mono_ae` resolves to the restricted-integral comparison. Correct.

## ScalarUniformNegativeLog.lean

**6. Variance mismatch: `stdGaussian` vs. `properCN1`.**
You state `stdGaussian(C)` has variance 1 per real coordinate, while the actual complex normal `CN(1)` model requires real/imaginary parts each to have variance `1/√2` (so that `E[|z|²] = 1`). If `complexNoncentralSampleSmallestEigenvalue M (by norm_num) z` interprets `z : ComplexSample 1 1` as having i.i.d. `N(0,1)` real/imaginary components under `stdGaussian _`, then the measure used here is **not** the standard complex Gaussian—it has twice the intended variance per complex entry. The small-ball bound `C = 1` from `actual_noncentralScalarCDF_le_threshold_uniform_mean` must have been proved against this exact same overscaled measure; otherwise the constant `1` in the conclusion `≤ 1` is wrong. Verify that the CDF lemma's measure and this integral's measure are literally the same object, not just both named `stdGaussian`.

**7. `M : Matrix (Fin 1) (Fin 1) ℂ` is a 1×1 matrix, not a scalar.**
You note "actual scalar mean M arbitrary fixed 1×1, NOT zero dimensions/general matrix." The type is fine, but `complexNoncentralSampleSmallestEigenvalue` for a 1×1 matrix returns `‖z - M₀₀‖²` (or similar). Confirm that the upstream definition doesn't degenerate or return a default when `m = n = 1` in a way that bypasses the intended noncentrality.

**8. `by norm_num` discharge of dimension proof.**
Used twice. If `norm_num` closes the goal, it's correct. But if the expected proof term is `rfl` or `decide`, `norm_num` may produce a different (though propositionally equal) proof. Since Lean uses proof irrelevance for propositions, this is harmless unless downstream definitional unfolding depends on the exact proof term. Unlikely here.

## Coordinator (Python)

**9. `validate_lock_data` double-reads source when `source_text` is None.**
`statements(source)` reads the file; then `check()` calls `validate_locks` which calls `validate_lock_data(lock)` without `source_text`, reading the file again. Between the two reads in `check()` (before and after `gated`), the file could change. You guard against this with `sha(source) != leaf["source_sha256"]`, which is correct. No vulnerability, just redundant I/O.

**10. Integration guard regex: `^import\s+<module>\s*$` with `re.M`.**
This correctly requires the locked module to appear as a direct import in `JinWishartFormalization.lean`. However, if the module path contains dots (e.g., `ProbabilityNegativeLogBounds`), `re.escape` handles it. The `\s*$` allows trailing whitespace but not inline comments like `-- needed`. This is intentional and correct.

**11. `exclusive()` context manager: expired claims are never cleaned.**
Your docstring says "Never take over or delete another owner's claim, including expired ones." This means a crashed coordinator leaves `.lock` files that permanently block re-runs until manual deletion. This is a design choice (fail-closed), not a bug, but it conflicts with the 15-minute deadline: if the lease expires without cleanup, the next run is blocked despite no active process. The `warnings.warn` is the only signal.

**12. `verify_acceptance` checks `facade.get("gated_helper_exit_code") != 0`.**
This key name `gated_helper_exit_code` must exactly match what `collaborative_check.py` writes. If the helper renames this field across versions, acceptance silently fails. Pin the receipt schema or validate keys exist before comparing.

**13. Axiom check: `set(d["axioms"]) - {"propext", "Classical.choice", "Quot.sound"}`.**
Correct whitelist. Note that `Quot.sound` appears only if quotient types are actually used; its presence is benign but worth confirming isn't injected spuriously by `noncomputable section`.

## Summary of Concrete Issues

| # | Severity | Location | Issue |
|---|----------|----------|-------|
| 1 | **High** | NegLogBounds | Missing `Measurable f` in first theorem |
| 6 | **High** | ScalarUniform | `stdGaussian` variance ≠ actual CN(1) variance |
| 4 | Medium | NegLogBounds | `probabilityTail` definition must match layer-cake form |
| 11 | Medium | Coordinator | Expired locks permanently block runs |
| 12 | Low | Coordinator | Receipt schema coupling |
| 2,3,5,7,8,9,10,13 | Info | Various | Confirmed correct or low risk |

Issues #1 and #6 are blocking. The rest are acceptable given stated premises.
