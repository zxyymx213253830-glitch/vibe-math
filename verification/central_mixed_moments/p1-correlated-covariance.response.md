# Hidden Assumptions, Three Routes, and Minimal Infrastructure

## Hidden Assumptions

1. **Invertibility of B is doing all the work.** The physical model A = ZB + M with B invertible means AB⁻¹ = Z + MB⁻¹ is standard uncorrelated. Every bound flows through this reduction. No assumption on rank(A) or M ≠ 0 is needed — B invertible forces (AB)ᴴ(AB) and AᴴA to have identical null-space structure up to the C(B) distortion.

2. **C(B) = max(1, ‖B‖²_F) is a deliberate over-approximation.** Using Frobenius/Euclidean CLM norm rather than operator norm means C(B) ≥ 1 + ‖B‖²_op in general. This is conservative but costs nothing for the moment criterion since p < k depends only on existence of finite bounds, not their tightness. The hidden assumption is that you never need C(B) to be sharp — only positive, even in B, and zero-free at B = 0.

3. **The CDF sandwich F_Mnorm(x/C(B)) ≤ F_corr(x) ≤ F_Mnorm(C(B⁻¹)·x) assumes the normalized mean MB⁻¹ is fixed deterministically.** This is valid because B and M are deterministic. No uniformity over growing condition number is claimed or needed. The hidden assumption is that existing `exactCNcomplexSampleMatrix` machinery already handles arbitrary fixed mean (including zero) — which it does per your checked assets.

4. **"No singular B claim" means the correlated model is defined only when B is full-rank square complex invertible.** If B were rectangular or singular, λ_min((AB)ᴴ(AB)) could collapse independently of λ_min(AᴴA), destroying both inequalities. This isn't an obstruction — it's the model boundary.

5. **Row vs. column orientation for CN.** For row-vector samples X (each row ~ CN(m, Σ)), the sample covariance is XᴴX/(n-1) and correlation structure lives in BᴴB under right factor X = ZB + M. For column-vector samples (each column ~ CN(m, Σ)), it's XXᴴ and the factor is BBᴴ. Your route uses column covariance via right multiplication AB, so the correct object is BᴴB. Using BBᴴ here would be the orientation error.

---

## Three Proof Routes for the Deterministic Inequalities

### Route 1: Operator Norm + Rayleigh (your current route)

**First inequality:** λ_min((AB)ᴴAB) ≤ C(B)·λ_min(AᴴA)

- Let w be unit eigenvector achieving λ_min(AᴴA), so ‖Aw‖² = λ_min(AᴴA).
- Set u = B⁻¹w. Then ABu = Aw.
- Rayleigh: λ_min((AB)ᴴAB)·‖u‖² ≤ ‖ABu‖² = ‖Aw‖² = λ_min(AᴴA).
- Operator norm: ‖w‖ = ‖Bu‖ ≤ ‖B‖_op·‖u‖, so 1 ≤ ‖B‖²_op·‖u‖² ≤ C(B)·‖u‖².
- Combine: λ_min((AB)ᴴAB) ≤ λ_min(AᴴA)/‖u‖² ≤ C(B)·λ_min(AᴴA).
- PSD non-negativity (λ_min ≥ 0) ensures no sign flip when multiplying through.

**Second inequality:** λ_min(AᴴA) ≤ C(B⁻¹)·λ_min((AB)ᴴAB)

- Apply the first inequality with (AB, B⁻¹) replacing (A, B): λ_min(((AB)B⁻¹)ᴴ(AB)B⁻¹) ≤ C(B⁻¹)·λ_min((AB)ᴴ(AB)).
- Left side is λ_min(AᴴA). Done.

**What's needed:** `exists_gram_minimum_unit_vector` (for w), `gramSmallestValue_rayleigh_lower` (for the Rayleigh step), submultiplicativity of operator norm, definition of C(B).

### Route 2: Loewner Order + Minimax

- B invertible implies (AB)ᴴ(AB) = BᴴAᴴAB. In Loewner order: λ_min(Bᴴ)·AᴴA ⪯ BᴴAᴴAB ⪯ λ_max(BᴴB)·AᴴA, i.e., σ²_min(B)·AᴴA ⪯ (AB)ᴴ(AB) ⪯ ‖B‖²_op·AᴴA.
- Taking λ_min: σ²_min(B)·λ_min(AᴴA) ≤ λ_min((AB)ᴴAB) ≤ ‖B‖²_op·λ_min(AᴴA).
- Since C(B) ≥ ‖B‖²_op ≥ σ²_min(B) and C(B⁻¹) ≥ 1/σ²_min(B), both target inequalities follow immediately.

**Advantage:** No eigenvector selection, no Rayleigh quotient argument. Pure PSD cone algebra.  
**What's needed:** Loewner ordering for congruence transforms (BᴴXB ⪰ σ²_min(B)·X for X ⪰ 0), min-max characterization of eigenvalues. This may require less infrastructure than Route 1 if Loewner monotonicity is already available.

### Route 3: Matrix Density / Jacobian Transformation

- View the map A ↦ AB as a diffeomorphism on ℂ^{m×N} with Jacobian |det(B)|^{2m}.
- The density of AB under A ~ CN(M, I⊗I) is proportional to exp(-tr((X-MB⁻¹)(X-MB⁻¹)ᴴ)) · |det(B)|^{-2m}, which is exactly CN(MB⁻¹, I⊗BBᴴ)... 

**Obstruction:** This route requires the change-of-variables formula for matrix-variate densities under right multiplication. For the *deterministic* inequalities on λ_min, density methods add nothing — they prove distributional identities, not pointwise spectral bounds. This route is relevant only if you want to derive the CDF sandwich from first principles rather than from the deterministic inequalities + known uncorrelated CDF. Since you already have `exactCNcomplexSampleMatrix` handling the uncorrelated case, Route 3 is unnecessary overhead for the inequalities themselves. It becomes relevant only for verifying the CDF sandwich normalization constants match.

---

## Minimal Typed Maps and Inverse Identities Required

You do **not** need a library of matrix identities. The minimal infrastructure is:

| Object | Type/Signature | Why needed |
|--------|---------------|------------|
| `C` | `(B : Matrix ℂ n n) → ℝ≥0` defined as `max 1 ‖B‖²_F` | Distortion constant; must satisfy C(B) ≥ 1, C(B) > 0, even in B |
| `gram` | `(A : Matrix ℂ m N) → Matrix ℂ N N` := AᴴA | PSD form whose λ_min we bound |
| `λ_min` | `(H : Matrix ℂ N N) → ℝ` (requires H Hermitian) | Minimum eigenvalue functional |
| `minEigvec` | `(H : Matrix ℂ N N) → {w : Fin N → ℂ // ‖w‖ = 1}` | Witness for Rayleigh equality; needs `exists_gram_minimum_unit_vector` |
| `mul_right` | `(A : Matrix ℂ m N) → (B : Matrix ℂ N N) → Matrix ℂ m N` | The map A ↦ AB |
| `inv` | `(B : Matrix ℂ n n) → [Invertible B] → Matrix ℂ n n` | Only used as B⁻¹ to define u = B⁻¹w and to apply Route 1 second inequality |

**Inverse identities required (exactly two):**

1. **(AB)B⁻¹ = A** — used to apply the first inequality to (AB, B⁻¹) yielding the second. No general inversion lemma needed; just right-cancellation.
2. **‖B⁻¹w‖ ≥ ‖w‖/‖B‖_op** (equivalently 1 ≤ ‖B‖_op·‖B⁻¹w‖) — this is the content of "operator norm gives 1 ≤ C(B)‖u‖²". Follows from submultiplicativity: ‖w‖ = ‖B(B⁻¹w)‖ ≤ ‖B‖_op·‖B⁻¹w‖.

That is the complete list. You do **not** need:
- Woodbury, Sherman-Morrison, or any block-inverse identity
- Rank conditions on A (the inequalities hold trivially when λ_min(AᴴA) = 0)
- M ≠ 0 (mean can be zero; MB⁻¹ = 0 is handled by existing arbitrary-mean machinery)
- SVD or polar decomposition of B
- Any identity relating C(B) to C(B⁻¹) beyond their independent definitions

---

## Genuine Obstructions Only

1. **None for the deterministic inequalities.** Routes 1 and 2 close with existing assets (`gramSmallestValue_rayleigh_lower`, `exists_gram_minimum_unit_vector`). The only requirement is B invertible, which is a model definition, not a proof gap.

2. **CDF sandwich transfer.** The step from deterministic λ_min bounds to F_corr sandwich requires that λ_min((AB)ᴴAB) and λ_min(AᴴA) are coupled on the same probability space with A random. Since B is deterministic, AB is a measurable function of A, so the pointwise inequalities lift directly to stochastic dominance: P(λ_min(AB) ≤ x) ≤ P(C(B)·λ_min(A) ≤ x) = P(λ_min(A) ≤ x/C(B)). This is measure-theoretic monotonicity, not a new probabilistic tool. **No obstruction.**

3. **Moment criterion transfer.** Given the CDF sandwich, E[λ_min(AB)^{-p}] < ∞ iff E[λ_min(A)^{-p}] < ∞ (with shifted arguments by C(B), C(B⁻¹) which are deterministic positive constants). The threshold p < k = m - N + 1 is invariant under positive scalar rescaling of the integrand. **No obstruction.**

4. **Route 3 is not needed and introduces no obstruction** — it's simply the wrong tool for pointwise spectral bounds. Use it only if you later need to verify density normalization of the correlated ensemble against the uncorrelated one.

5. **Covariance orientation is a definition-level choice, not a proof obstruction.** Your model uses column vectors with right factor B, giving column covariance BᴴB. If someone writes the model with row vectors and right factor B, the row covariance is BBᴴ. These are different models. The inequalities you state are correct for the column model. No contradiction exists — only potential confusion if mixing conventions mid-proof.

**Bottom line:** There are zero genuine mathematical obstructions. The proof closes with Route 1 (or 2), two inverse identities, the typed maps above, and direct lifting of deterministic inequalities through monotonicity of probability measures. No new target density, no G₂ functionals, no uniform condition-number control, and no rank/M assumptions are required.
