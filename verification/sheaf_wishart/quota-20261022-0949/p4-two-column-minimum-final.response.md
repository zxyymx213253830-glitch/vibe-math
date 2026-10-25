# P4 Adversarial Review: ActualCentralTwoColumnMinimum.lean

## 1. Hardcoded Dimension Mismatch (Critical)

The file's stated purpose is "all-row two-column minimum," yet the main theorems hardcode `m := d+2` and `n := 2` throughout (`actualCentralTwoColumn_minimum_tail_momentDet`, `theorem1CentralTwoColumn_candidate_eq_actualCDF`). The parameter `d : ℕ` controls only the tail measure exponent, not the row count generically. The claim of generality across "all rows" is unsupported by the actual statements, which are specialized to exactly `d+2` rows. If the intent was arbitrary row counts, these theorems do not deliver it.

## 2. Unjustified Restriction to Ordered Region (Mathematical Gap)

In `min_weighted_ordered_integral`, the right-hand side integrates over `{z | z.2 < z.1}` (the ordered region O), but the left-hand side involves `(centralTwoColumnJointEigenvalueLaw d) {y | x < y.2}`, which measures the event that the *minimum* eigenvalue exceeds `x` without any ordering constraint on the integration domain. The proof bridges this via `hsets : P ∩ S = R ∩ O`, where `S = {z | 0 < z.2 ∧ z.2 < z.1}`. This set equality is correct, but the semantic step—replacing an integral over the full support with one over the strictly ordered region `z.2 < z.1`—relies on the joint density being supported *only* on ordered pairs or the unordered contribution being zero. The density definition `centralTwoColumnEigenvalueDensity` includes a conditional `if 0 < z.2 ∧ z.2 < z.1`, which does restrict support, but this means the "joint eigenvalue law" as stated is *defined* via ordered coordinates only. For a minimum statistic, this is mathematically valid only if the eigenvalues are labeled such that `y.2` is always the minimum. The code assumes this labeling convention silently; it should be an explicit hypothesis or definitional guarantee from `centralTwoColumnEigenpair`.

## 3. Missing Positivity Hypothesis on `d` (Potential Gap)

The constant `C = d! * (d+1)!` appears in denominators (`eq_div_iff hC.ne'`). While `positivity` discharges `0 < C` for all `d : ℕ` (including `d = 0`, where `C = 1`), the integrability conditions `powerExponentialTail_integrable_pow d x 1` and `... 2` are passed as arguments. Whether these hold for `d = 0` is deferred to the caller. No logical error here, but the theorem's applicability to `d = 0` depends entirely on whether those imported integrability lemmas cover it—this is a dependency fragility, not a self-contained guarantee.

## 4. Use of `ENNReal.toReal` Without Finiteness Proof (Gap)

`have hr := congrArg ENNReal.toReal h` applies `toReal` to both sides of an ENNReal equality. This is valid only if both sides are finite (not `⊤`). The left side involves `(centralTwoColumnJointEigenvalueLaw d) P` scaled by factorials; the right side is an integral of a nonnegative function. Finiteness is implicitly guaranteed because the measure is a probability law and the integrand has established integrability, but **this finiteness is never explicitly invoked or proven before applying `toReal`**. If either side were `⊤`, `toReal` would yield `0` and the subsequent division manipulation would be unsound. A `have hfin : ... ≠ ⊤` guard is missing.

## 5. Complement Set Arithmetic Is Correct but Fragile

The step `probReal_add_probReal_compl` followed by `linarith` to extract the CDF from the tail moment is arithmetically sound. However, `theorem1CentralTwoColumn_PsiDet_zero` is invoked without its statement visible; if it carries unstated preconditions (e.g., `d > 0`), they propagate silently here.
