# P4 Adversarial Review: Issues Only

## HermitianInverseTrace.lean

**1. `eigenvalues` vs `eigenvalues₀` scope mismatch (critical)**
The proof constructs `D` and `E` using `hA.eigenvalues` (the unordered multiset-to-function lift), then attempts to transfer the final sum to `hA.eigenvalues₀` (the ordered/sorted eigenvalue array) via a single `Equiv.sum_comp` at the end. This equiv is generated from `Fintype.card_fin`, which produces *some* equivalence between `Fin n` and itself—not necessarily the permutation that relates the unordered indexing to the ordered indexing. The reindexing step is therefore unjustified unless one separately proves that the specific equiv produced coincides with the sorting permutation, which is not done here.

**2. `map_mul` / `map_pow` / `map_one` ambiguity**
`Unitary.conjStarAlgAut ℂ _ U` is applied as a function, but the lemmas `map_mul`, `map_pow`, `map_one` require it to be recognized as a `RingHom` or `AlgHom`. The code relies on coercion and typeclass inference to supply the homomorphism structure. If the coercion does not fire definitionally, these rewrites silently fail or close over a different instance than intended. This is fragile and version-dependent.

**3. `hnz` quantifies over wrong index source**
`hnz : ∀ i, hA.eigenvalues₀ i ≠ 0` asserts nonvanishing of the *ordered* eigenvalues, but `have hn (i : Fin n) : hA.eigenvalues i ≠ 0 := hnz _` applies it directly to the *unordered* eigenvalues by passing the same `Fin n` index. This is only valid if `eigenvalues` and `eigenvalues₀` share the same indexing up to the identity, which they do not—they differ by a permutation. The nonzero hypothesis is being applied to the wrong family.

**4. Zero-dimension edge case (`n = 0`)**
When `n = 0`, `Fin 0` is empty. The theorem statement reduces to `0 = 0` (empty trace, empty sum), which is true, but `hnz` becomes vacuously satisfied while `A⁻¹` for a `0 × 0` matrix involves `IsUnit A` reasoning that may not be definitionally trivial. Not a bug per se (zero dimensions are intentional), but the `classical` block and spectral theorem invocation were not designed with this degeneracy in mind.

---

## LogOneAddTaylorBounds.lean

**5. `interior_subset` misuse in monotonicity argument**
In `nonneg_of_nonneg_derivative_on_nonneg`, the call `(hd x (interior_subset hx))` passes a proof that `x ∈ interior (Ici 0)` into `hd`, which expects `0 ≤ x`. But `interior_subset hx` yields `x ∈ Ici 0`, i.e., `0 ≤ x`, only when `hx : x ∈ interior (Ici 0)`. The variable `hx` in the lambda `fun x hx => ...` ranges over `x ∈ Ici 0`, **not** `x ∈ interior (Ici 0)`. The code applies `interior_subset` to a point that may lie on the boundary `x = 0`, where `interior_subset` does not apply. This is a genuine gap: the derivative hypothesis `hd` is available on the closed ray, but `monotoneOn_of_hasDerivWithinAt_nonneg` requires `HasDerivWithinAt` on the interior, and the boundary point `0` is mishandled.

**6. Dependency on unverified imported lemma**
`log_one_add_quadratic_gap_bounds` uses `(log_one_add_linear_gap_bounds u hu).1` in its final `exact`. This lemma is imported from `LogDetLowScaleSecondOrder` and is not reproved here. The correctness of the lower bound `0 ≤ u - log(1+u)` depends entirely on that external result. Per instructions, imported results are separately checked, but note that this module's theorem is incomplete without it.

**7. Derivative computation correctness (minor, verified)**
The `convert h using 1` blocks in both `hd` proofs rely on `field_simp` and `ring` to close derivative simplification goals. These are algebraically correct for `x ≥ 0` (where `1 + x > 0`), and `positivity` discharges the denominator obligation. No issue here, but the `convert` pattern masks what would otherwise be explicit `congr_arg` steps.

---

## Cross-cutting

**8. No rank/dimension/mean errors detected** — consistent with the stated setup (fixed `B:p×n`, `M:m×n`, etc.). The theorems here are purely algebraic/analytic and do not touch the Wishart rank conditions.

**9. Polynomial null sets / Fubini / model correspondence** — correctly noted as `[需人工审查]`; nothing in these two files invokes measure theory or Fubini, so no new exposure is introduced here.
