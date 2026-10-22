# P1 Route Review: Square-Integrability of log ||P||

## Assessment of the Candidate Route

The route is structurally sound but contains several hidden hypotheses and failure modes that need addressing before it can be considered complete.

## Step-by-Step Analysis

**Step 1 (Layercake):** Valid as stated. The exponential tail bound P(Y≥t)≤C·exp(-t) gives E[Y²]≤2C by layercake integration, regardless of positivity of f. However, **hidden hypothesis**: the constant C must be uniform across all sections in later steps. If C depends on parameters that vary with n or degree, the induction fails. Verify that the linear smallball constant is truly absolute for planar Gaussians.

**Step 2 (Root factors):** The conclusion E[(log⁻||z-a||²)²]≤const is correct for fixed a under standard complex Gaussian. **Failure mode**: when a itself becomes random in later induction steps, you need the bound uniform over a—which you have from Step 1's setup—but also measurable dependence. The factor of 1/4 depends on normalization of the Gaussian variance; confirm your stdGaussian(C) convention matches.

**Step 3 (Polynomial factorization):** This is the most delicate step. **Hidden hypotheses:**
- Leading coefficient a≠0 almost surely: you note nonzeroAE, but for random polynomials in n variables, the leading coefficient is itself a polynomial evaluation in n-1 variables. The induction must guarantee this remains nonzeroAE at each stage.
- Cauchy-Schwarz application: (Σ neglog root_j)² ≤ d·Σ(neglog root_j)² requires roots counted with multiplicity. For d=0 (constant polynomial), the bound should collapse cleanly—verify your totalized log0=0 convention handles this without 0·∞ indeterminacy.
- **Normalization gap**: the bound 2(neglog a)² + d²/2 assumes unit-variance roots. If leading coefficient has different scale, you pick up log(scale) terms.

**Step 4 (Parameterized sections):** "No measurable root choice" is correctly identified—roots appear only in pointwise estimates, not as measurable selections. **Hidden hypothesis**: you need the coefficient-to-polynomial map to be Borel measurable so that neglog of coefficients is jointly measurable. The domination 2·coeff²+D²/2 works only if D is deterministic (fixed degree bound). For random degree, integrability of D² becomes an additional requirement.

**Step 5 (Induction via finSuccEquiv):** **Critical failure mode**: separating one variable z_n from the rest, P(z_1,...,z_n) = Σ c_k(z_1,...,z_{n-1})·z_n^k. The leading coefficient c_d is a polynomial in n-1 variables. You need:
- c_d ≠ 0 a.e. (given by nonzeroAE asset)
- E[(log⁻|c_d|)²] < ∞ (this is the inductive hypothesis applied to c_d)
- But c_d has lower degree than P, so the induction is on both n and degree simultaneously. Make this double induction explicit.

Upper positive log domination by ||P||² integrability is valid since log⁺(x) ≤ x for x≥1, giving (log⁺||P||)² ≤ ||P||² eventually.

## Alternatives

- **MemLp/Hölder route**: Instead of factorization, use that ||P||^{-s} ∈ L¹ for small s>0 (from smallball) and interpolate. Hölder gives E[(log⁻||P||)²] ≤ lim_{s→0} E[||P||^{-s}]/s² type bounds. This avoids root measurability entirely but requires quantitative control of the smallball exponent as n grows.
- **Direct smallball**: If you have P(||P||≤ε) ≤ C·ε^α uniformly, then E[(log⁻||P||)²] ≤ 2C/α² directly. Your current assets give this for linear factors; extending to general P without factorization would require the Jacobian/determinant structure you're deferring to later transport.

## Recommended Minimal Interfaces

1. `HasLogNegSquareIntegrable : Type → Prop` — predicate asserting E[(log⁻||·||)²]<∞, closed under products and sums with explicit degree tracking
2. `SmallballExponent α` — uniform exponent for P(||f||≤ε)≤C·ε^α, composable under multiplication
3. `LeadingCoeffNonzeroAE` — bundled with square-log-integrability of the coefficient itself, forming the inductive package
4. `TotalizedLogZero` — definition-level handling of log 0 = 0 propagated through all interfaces to avoid case splits

## Summary

The route works modulo: (a) making the double induction on (n, degree) explicit, (b) verifying normalization constants are truly uniform, (c) ensuring the leading-coefficient inductive step doesn't create circular dependencies. No step currently asserts a completed proof.
