# Analysis of Hard-Edge Diversity Exponent Routes

## (1) Hidden Hypotheses, Counterexamples, and Inequality Directions

**The deterministic sandwich conjecture:**
min_j D_j ≤ n · λ_min(A^H A) ≤ n · max_j D_j  [conjectured]
λ_min(A^H A) ≤ D_j for every j  [conjectured lower bound]

**Hidden hypotheses and issues:**

- **Column normalization implicit assumption.** The inequality |u_j|√(D_j) ≤ √(λ_min) requires careful tracking. If u is a unit eigenvector of A^H A with eigenvalue λ_min, then ‖Au‖² = λ_min. Writing Au = Σ u_k a_k (columns), the projection onto the orthogonal complement of span(a_i : i≠j) gives |u_j|·‖P_{j⊥} a_j‖ = |u_j|√(D_j). But ‖P_{j⊥}(Au)‖ ≤ ‖Au‖ = √(λ_min), so |u_j|√(D_j) ≤ √(λ_min). This direction appears **correct**. Since max_j |u_j| ≥ 1/√n, we get min_j D_j ≤ n·λ_min. **This half seems valid.**

- **Reverse direction is the hard one.** λ_min ≤ D_j for all j requires showing the minimum eigenvalue is controlled by *every* leave-one-out residual. This is plausible via Rayleigh quotient: λ_min = min_{‖v‖=1} ‖Av‖², and choosing v = e_j gives ‖Ae_j‖² = ‖a_j‖², which is NOT D_j (D_j is the squared distance to the span of others, not the norm). The correct test vector for D_j involves the projection residual, but this doesn't directly give λ_min ≤ D_j without additional structure. **This direction needs scrutiny; it may require A to have full column rank or specific generic position assumptions.**

- **n=1 boundary.** When n=1, D_1 = ‖a_1‖² and λ_min = ‖a_1‖², so equality holds trivially. The "complement of other columns" is the whole space. Must be handled as a base case.

- **Linear dependence.** If columns are linearly dependent, some D_j = 0 and λ_min = 0; inequalities hold trivially but the Gamma(d+1,1) law for D_j assumes the Wishart/Gaussian structure where d = m-n ≥ 0 ensures full rank almost surely.

- **Counterexample risk for reverse bound.** Consider n=2, d=0 (square). Then D_j are not independent of λ_min in a simple multiplicative way. The factor "n" in n·λ_min may not be tight. I am not aware of a clean counterexample breaking λ_min ≤ D_j, but the constant could be dimension-dependent in ways not captured by a bare "1".

**Exact inequality directions (my assessment):**
- |u_j|√(D_j) ≤ √(λ_min): **Correct** (projection reduces norm).
- λ_min ≤ D_j for all j: **Likely correct for Gaussian/Wishart almost surely**, but the deterministic statement for arbitrary A may fail if A has special structure. For CN(0,1) entries, D_j ~ Gamma(d+1,1) marginally, and λ_min > 0 a.s. when d≥0.
- min_j D_j ≤ n·λ_min: **Correct** (follows from first inequality + pigeonhole on |u_j|).
- λ_min ≤ min_j D_j: **Direction uncertain deterministically**; probabilistically for Wishart this should hold with high probability but the constant matters.

---

## (2) Comparison of Three Routes

### Route A: Residual/Gamma Sandwich (Diversity Exponent d+1)

**Mechanism.** Use GammaCDF_{d+1}(x) ≤ F(x) ≤ min(1, n·GammaCDF_{d+1}(nx)). Since GammaCDF_{k}(x) ~ x^k/k! as x→0, both bounds are Θ(x^{d+1}), giving logarithmic diversity exponent d+1 without exact leading coefficient.

**Strengths.** Avoids spectral Jacobian entirely. Uses only marginal laws of D_j (already proved: Gamma(d+1,1)) and deterministic linear algebra inequalities. Directly leverages existing Lean assets for Gamma CDF and factorial functionals.

**Weaknesses.** Does NOT yield exact T4 coefficient (as noted, n=2,d=1 gives 1.5 vs lower-Gamma constant 0.5 — the sandwich is loose by a polynomial factor). Requires proving the deterministic inequalities in Lean, including handling the n=1 edge case and the "for all j" quantifier. The upper bound uses union-bound-style logic (min of n variables) which introduces the factor n inside the CDF argument.

### Route B: Analytic Polynomial Derivative Cancellation

**Mechanism.** F(x) = 1 - exp(-nx)Q(x) with Q a fixed polynomial of degree nd, Q(0)=1, leading coefficient 1/M. Extract left-tail behavior by Taylor-expanding 1 - exp(-nx)Q(x) around x=0. The x^{d+1} coefficient emerges from cancellation between exp(-nx) and Q(x) derivatives at 0. Specifically, F(x)/x^{d+1} → (some expression in Q^{(k)}(0) for k≤d+1 and n).

**Strengths.** Can yield **exact** leading coefficient, not just order. Uses the already-proved polynomial structure (Q exists, degree nd, Q(0)=1). Purely analytic/algebraic once Q's low-order coefficients are identified. No new probabilistic machinery.

**Weaknesses.** Requires knowing Q^{(k)}(0) for k up to d+1, which means extracting specific coefficients from the product formula M = Π_j (j+d)!/j!. This is a nontrivial algebraic computation. For general d, identifying the (d+1)-th derivative of Q at 0 from the factorial product may require new combinatorial identities. The d=0,1 cases are done; general d is open. **This is likely the hardest route algebraically.**

### Route C: Full Cone-Boundary/Spectral Integration

**Mechanism.** Integrate the joint eigenvalue density over the region {λ_min ≤ x} using the Weyl integration formula / spectral Jacobian G2. This is the "standard" random matrix theory approach.

**Strengths.** Conceptually complete; would give exact density and all tail coefficients simultaneously. Connects to classical Selberg/Aomoto integral technology.

**Weaknesses.** **G2 (general Weyl spectral Jacobian) is explicitly stated as NOT proved in Lean.** This route requires a new spectral change of variables, which the prompt says to avoid ("without a new spectral change of variables"). Heaviest lift in terms of new formalization. Blocked until G2 is available.

---

## (3) Minimal Lean Obligations and Weak Links per Route

### Route A: Residual/Gamma Sandwich

| Obligation | Type | Status |
|---|---|---|
| Deterministic inequality: ∀j, λ_min ≤ D_j (or appropriate direction) | Linear algebra | **NEW, weak link** |
| Pigeonhole bound: min_j D_j ≤ n·λ_min via eigenvector | Linear algebra | NEW but follows from above |
| n=1 base case (D_1 = λ_min exactly) | Boundary | Trivial |
| Marginal law D_j ~ Gamma(d+1,1) for actual Gaussian A | Probabilistic | **Already proved** (per prompt) |
| GammaCDF asymptotics: GammaCDF_{d+1}(x) = Θ(x^{d+1}) | Analysis | Known integration asset |
| Union/min bound for CDF of minimum | Probabilistic | Standard (Boole-type) |
| Sandwich ⇒ log diversity exponent d+1 | Interpretation | Human-level deduction |

**Weak link:** The deterministic inequality proof in Lean. Requires reasoning about projections, eigenvectors, and the "span of other columns" construction formally. Not conceptually deep but tedious. All probabilistic ingredients are existing assets.

### Route B: Analytic Polynomial Derivative Cancellation

| Obligation | Type | Status |
|---|---|---|
| Q(0) = 1, deg Q = nd, leading coeff 1/M | Algebraic | **Already proved** |
| Extract Q^{(k)}(0) for k=1,...,d+1 from M = Π(j+d)!/j! | Algebraic/combinatorial | **NEW, major weak link** |
| Taylor expansion of 1-exp(-nx)Q(x) to order d+1 | Analysis | Routine |
| Cancellation pattern yielding exact x^{d+1} coefficient | Algebraic | Follows from above |
| Verify against d=0 (Exp(n)) and d=1 (n(n+1)/4) | Sanity check | Already proved cases serve as tests |

**Weak link:** The combinatorial extraction of low-order Taylor coefficients of Q from the factorial product. This is exact algebra, not analysis, but requires identities that may not exist in current Lean libraries. No new probability needed. Entirely self-contained but potentially very hard for general d.

### Route C: Full Cone-Boundary/Spectral Integration

| Obligation | Type | Status |
|---|---|---|
| General Weyl spectral Jacobian G2 | Geometric/analytic | **NOT proved** (stated blocker) |
| Joint eigenvalue density for rectangular Wishart | Spectral theory | Depends on G2 |
| Integration over {λ_min ≤ x} cone | Multivariate analysis | NEW |
| Selberg-type integral evaluation | Special functions | UNVERIFIED availability in Lean |
| Asymptotic extraction of left tail | Analysis | Follows if above available |

**Weak link:** G2 itself. Everything downstream is blocked. This route has the most genuinely new obligations and is explicitly out of scope per the prompt's constraint.

---

## (4) Recommendation

**Route A (Residual/Gamma Sandwich) has the smallest genuinely NEW obligations.**

Reasoning:
- It requires **one** new deterministic lemma (the eigenvector/projection inequality relating λ_min to D_j), which is finite-dimensional linear algebra with no spectral change of variables.
- All probabilistic ingredients (D_j ~ Gamma(d+1,1), Gamma CDF properties, factorial functional) are **already proved** per the prompt's inventory.
- It does NOT require extracting combinatorial identities from factorial products (Route B's blocker) nor proving G2 (Route C's blocker).
- The output is weaker (order x^{d+1} but not exact coefficient), but this matches the stated goal: "meaningful general hard-edge progress" and "diversity exponent d+1."

**Caveat:** The user correctly notes n=2,d=1 exact constant 1.5 differs from the lower-Gamma sandwich constant 0.5. This confirms the sandwich gives the **exponent** but not the **sharp prefactor**. If exact T4 is eventually needed, Route B becomes necessary, but it should be deferred until the combinatorial coefficient extraction is better understood.

**Recommended sequence:** Prove Route A's deterministic inequality in Lean (handling n=1 as base case), invoke existing Gamma assets, establish diversity exponent d+1. Flag the gap between sandwich constants and exact coefficients as future work requiring Route B. Do not attempt Route C until G2 is independently resolved.
