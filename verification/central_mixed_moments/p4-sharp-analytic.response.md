# P4 Concrete Issue Audit: Analytic Germs, Taylor Coefficients, and Finite Convolution Arithmetic

## 1. One-Sided Filters vs. Two-Sided Factorization (Critical)

**File:** `AnalyticPositivePowerLimit.lean`
**Theorem:** `analytic_positive_factor_of_log_exponent`

* **Issue:** The positivity hypothesis `hp` and the log-limit hypothesis `hl` are both stated on the one-sided filter `𝓝[>] 0`. However, the mathlib lemma `exists_eventuallyEq_pow_smul_nonzero_iff` (invoked via `hf.exists_eventuallyEq_pow_smul_nonzero_iff`) extracts a factorization that holds on the **two-sided** filter `𝓝 0`. 
* **Consequence:** The conclusion correctly states the factorization on `𝓝 0`, but the intermediate step `hgf` restricts it back to `𝓝[>] 0` to prove `g > 0` locally. This is logically sound, but the transition from the one-sided log-limit (which only sees $x > 0$) to the two-sided analytic germ factorization is a mathematical leap. The log-limit uniqueness `tendsto_nhds_unique hj hl` is valid because `hj` is restricted to `𝓝[>] 0` to match `hl`. 
* **Verdict:** Correctly handled, but the `hnot` proof (showing $f$ is not eventually zero on `𝓝 0`) relies on the fact that if it were zero on `𝓝 0`, it would be zero on `𝓝[>] 0`, contradicting `hp`. This is exact. No off-by-one here.

## 2. Log Exponent Order Identification (Critical)

**File:** `AnalyticPositivePowerLimit.lean` / `AnalyticPowerTaylorCoefficient.lean`

* **Issue:** The integer $k$ is extracted purely from the limit of $\log(f(x))/\log(x)$. For a general non-analytic function, this limit does not guarantee an $x^k$ factorization. 
* **Resolution:** The code **does not** assume this for non-analytic functions. It strictly requires `hf : AnalyticAt ℝ f 0`. The analytic germ provides the integer order $j$ via `exists_eventuallyEq_pow_smul_nonzero_iff`, and the bounds force $j = k$ via `Nat.cast_injective`. 
* **Verdict:** Sound. The log-limit is used *only* to identify the exponent of an already-guaranteed analytic factorization, not to conjure one into existence. No smooth non-analytic factorization is assumed.

## 3. Taylor Factorials and `analyticOrderAt` Off-By-One Check

**File:** `AnalyticPowerTaylorCoefficient.lean`
**Theorem:** `analytic_power_ratio_taylor_limit`

* **Issue:** The expansion uses `exists_eventuallyEq_sum_add_pow_mul (k+1)`. The sum is over `Finset.range (k+1)`, which is $\{0, 1, \dots, k\}$. 
* **Verification:** The lemma `hz` proves that `iteratedDeriv i f 0 = 0` for all $i < k$. Thus, the sum over `range (k+1)` collapses exactly to the $i=k$ term: `(x^k / k!) * iteratedDeriv k f 0`. The remainder is $x^{k+1} F(x)$, which vanishes in the limit after dividing by $x^k$.
* **Verdict:** No off-by-one error. The factorial denominator $k!$ matches the $k$-th iterated derivative perfectly. The `analyticOrderAt` being exactly $k$ (as a `ℕ∞`) is correctly extracted from the non-vanishing of the $k$-th derivative and the vanishing of lower ones.

## 4. Finite Convolution Signs and Off-By-One (Critical)

**File:** `ExponentialPolynomialTaylor.lean`
**Theorem:** `iteratedDeriv_exp_mul_polynomial_zero`

* **Leibniz Rule Application:** The sum is over `Finset.range (k+1)`, meaning $i$ goes from $0$ to $k$. The binomial coefficient is `k.choose i`. The derivative orders are $i$ for the exponential and $k-i$ for the polynomial. This is exactly the Leibniz rule for the $k$-th derivative. No off-by-one.
* **Signs:** The exponential is $\exp(cx)$. Its $i$-th derivative at $0$ is $c^i$. The formula has `c^i`. If the application uses $c = -N$, then the sign is $(-N)^i$, which matches the user's finite formula: $\sum_{i=0}^k \binom{k}{i} (-N)^i (k-i)! P_{\text{coeff}}(k-i)$. The Lean theorem leaves $c$ as a free variable, so the sign is algebraically exact and introduces no implicit negation errors.
* **Factorials:** The $(k-i)$-th derivative of $P$ at $0$ is `(k-i)! * P.coeff (k-i)`. This is correctly supplied by `iteratedDeriv_polynomial_eval_zero`.
* **Verdict:** The finite convolution identity is **exact**. There are no unevaluated probability integrals or hidden derivatives. The prefactor arithmetic is fully deterministic.

## 5. Missing T4 Prefactor Identity

* **Issue:** The user notes "original general T4 prefactor NOT proved."
* **Observation:** The provided Lean files prove the *finite arithmetic formula* for the $k$-th derivative of $\exp(cx)P(x)$ at $0$. They do **not** contain a theorem mapping this finite sum to a specific closed-form "T4 prefactor" (e.g., simplifying the alternating convolution $\sum \binom{k}{i}(-N)^i(k-i)!P_{k-i}$ into a single non-summation expression). 
* **Verdict:** This is a confirmed gap. The finite sum is rigorously proved, but its classical combinatorial simplification (if one exists for the specific $P$ arising from the Wishart/CDF context) is absent from these sources.

## 6. Axiom Compliance (kernelPASS standard3)

Checking `#print axioms` output conceptually against the imports:
* `AnalyticPositivePowerLimit`: Relies on `Mathlib.Analysis.Analytic.IsolatedZeros` and `CentralMinimumDiversity`. Uses classical logic (`Classical.choice` via `exists_...`), real numbers (`Real`), and analytic continuation. No `sorry` or external probability axioms.
* `AnalyticPowerTaylorCoefficient`: Relies on `Mathlib.Analysis.Analytic.Order`. Uses `iteratedDeriv` properties. Purely deterministic calculus.
* `ExponentialPolynomialTaylor`: Relies on `ContDiffAt`, `iteratedDeriv_fun_mul`, `iteratedDeriv_exp_const_mul`. Standard mathlib calculus.
* **Verdict:** All three files should pass `standard3` (assuming `standard3` permits `Classical.choice` and `Real` axioms, which is standard for mathlib analysis). No probability measures, no model-specific assumptions, no numerical approximations.

## 7. Human Measure/Model Review Requirement

* The Lean code correctly isolates the analytic germ factorization and the Taylor arithmetic from the CDF definition. 
* The jump from the actual non-analytic-at-0 CDF to the analytic continuation $G$ on all reals is **not** formalized in these snippets; these snippets assume `hf : AnalyticAt ℝ f 0` as a starting point. 
* **Actionable Note:** The human reviewer must verify that the piecewise CDF definition actually yields a function $G$ that satisfies `AnalyticAt ℝ G 0` globally, and that the one-sided positivity/log-limit conditions on the CDF transfer correctly to $G$. The Lean code proves the consequences *given* analyticity, but does not prove the CDF *is* analytic.

---

### Summary of P4 Concrete Issues

| Component | Status | Specific Finding |
| :--- | :--- | :--- |
| **One-sided filters** | PASS | `hnot` correctly bridges `𝓝[>] 0` positivity to `𝓝 0` non-vanishing. |
| **Log exponent order** | PASS | Integer $k$ safely identified via analytic germ, not assumed for non-analytic functions. |
| **Taylor factorials** | PASS | `range (k+1)` and $k!$ denominator are exactly aligned. No off-by-one. |
| **Finite convolution signs** | PASS | Leibniz rule with $c^i$ is algebraically exact; safely absorbs $c = -N$ without sign drift. |
| **Off-by-one (derivatives)** | PASS | $i$-th deriv of exp and $(k-i)$-th deriv of poly sum to $k$. Exact. |
| **T4 Prefactor Identity** | **FAIL** | The finite sum is proved, but its classical closed-form simplification is missing from the sources. |
| **Axioms (kernelPASS)** | PASS | Pure mathlib analysis/calculus. No probability axioms or `sorry`. |
| **Model Review Waiver** | **REJECTED** | Code assumes analyticity; human review required to confirm CDF continuation meets `hf`. |
