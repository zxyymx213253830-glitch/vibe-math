# Critique of Candidate A for Wide Expected Prelog Extension

## Setup and Target

We have $X \in \mathbb{C}^{m \times N}$ with iid $\mathcal{CN}(M_{ij}, 1)$ entries (variance-one, so real/imaginary parts each have variance $1/2$, hence the $1/\sqrt{2}$ scaling on the standard Gaussian source). The functional is:

$$C(\rho) = \mathbb{E}\left[\log\left(\operatorname{Re}\det(I_N + \rho X^H X)\right)\right]$$

For $m \geq N > 0$: expected prelog is $N$, finite offset is $\mathbb{E}[\log\det(X^H X)]$ (the logdet Gram).

**New target**: For wide matrices $m < N$ (both dimensions positive), extend the expected prelog to $\min(m, N) = m$. The wide offset must use $\mathbb{E}[\log\det(XX^H)]$, not the singular $X^H X$ which has rank at most $m < N$.

---

## Candidate A: Deterministic Transpose Route

**Claim chain**: $(X^T)^* X^T = \bar{X} X^T$... wait, let me be precise. The candidate argues:

1. **Deterministic identity**: For any complex matrix $X$, the "complex Gram" satisfies a transpose relation. Specifically, if we define the Gram as $X^H X$ (tall) vs $XX^H$ (wide), then via Sylvester's determinant identity (`Matrix.det_one_add_mul_comm`):
$$\det(I_N + \rho X^H X) = \det(I_m + \rho XX^H)$$
for any scalar $\rho$ (real or complex—here $\rho$ is real and positive). This is exact, no expectations yet.

2. **Functional equality**: Therefore $C_X(\rho) = \log(\operatorname{Re}\det(I_N + \rho X^H X)) = \log(\operatorname{Re}\det(I_m + \rho XX^H))$ deterministically for real $\rho > 0$. So the *random variable* inside the expectation is identical whether you view $X$ as tall or wide.

3. **Source transpose reindex**: `complexSampleTransposeReindex m n` is a real linear isometry equivalence that swaps row/column indexing on the underlying $2mn$-dimensional real Euclidean space. Applying `stdGaussian_map` of that isometry preserves the standard Gaussian measure.

4. **Mean transformation**: Under this transpose reindex, $X \mapsto X^T$ (not $X^H$), so the mean matrix transforms as $M \mapsto M^T$ (not $M^H$). The distributional statement is:
$$X \sim \mathcal{CN}(M, I) \text{ on } \mathbb{C}^{m \times N} \implies X^T \sim \mathcal{CN}(M^T, I) \text{ on } \mathbb{C}^{N \times m}$$

5. **Conclusion attempt**: The expected wide $C$ for shape $(m, N, M)$ equals the expected tall $C$ for shape $(N, m, M^T)$. Since the tall case has prelog $N$ when $N \leq m$... but here $m < N$, so the transposed shape $(N, m)$ has $N > m$, meaning the transposed matrix is *also* wide (or square-ish the wrong way). 

**Wait—this is the critical flaw.** If $m < N$, then $X^T \in \mathbb{C}^{N \times m}$ with $N > m$. The transposed matrix is tall! So the tall prelog result applies to $X^T$: its expected prelog is $\min(N, m) = m$. ✓

So actually the logic closes:
- Wide $X \in \mathbb{C}^{m \times N}$, $m < N$: want prelog $m$.
- $X^T \in \mathbb{C}^{N \times m}$, $N > m$: this is tall, known prelog = $\min(N, m) = m$. ✓
- Sylvester gives $C(X) = C(X^T)$ pointwise.
- Transpose reindex preserves Gaussian, shifts mean $M \to M^T$.
- Therefore $\mathbb{E}_M[C(X)] = \mathbb{E}_{M^T}[C(X^T)] = \mathbb{E}_{M^T}[\text{tall prelog } m + \text{offset}]$.

---

## Exact Assumptions, Risks, and Minimal Obligations

### What Candidate A Actually Needs (Obligations)

| # | Obligation | Status / Risk |
|---|-----------|---------------|
| 1 | `Matrix.det_one_add_mul_comm` (Sylvester): $\det(I_N + AB) = \det(I_m + BA)$ for $A: m \times N$, $B: N \times m$ | **Available**. Set $A = \sqrt{\rho} X^H$, $B = \sqrt{\rho} X$. Works for any commutative ring. No risk. |
| 2 | Determinant transpose invariance: $\det(A) = \det(A^T)$ | **Not needed directly** if using Sylvester as stated. But if the candidate conflates $(X^H X)^T$ with $XX^H$, there's a risk. Actually $(X^H X)^T = X^T \overline{X}$, which is NOT $XX^H$ in general. The candidate must use Sylvester, not naive transpose-of-Gram. |
| 3 | `complexSampleTransposeReindex m n` is a real-linear isometry on the $2mn$-dim source | **Pinned asset**. Stated as given. |
| 4 | `stdGaussian_map` of that isometry preserves the standard Gaussian measure | **Pinned asset**. Follows from isometry + Gaussian invariance under orthogonal maps. |
| 5 | The $1/\sqrt{2}$ scaling: std Gaussian on $\mathbb{R}^{2mn}$ maps to $\mathcal{CN}(0,1)$ entries | **Essential and correct**. Variance-one complex Gaussian has real/imag parts each $\mathcal{N}(0, 1/2)$. The source is standard normal on $\mathbb{R}^{2mn}$, scaled by $1/\sqrt{2}$ per complex entry. The isometry must respect this. |
| 6 | Mean becomes $M^T$ not $M^H$ under transpose reindex | **Correct**. Transposition (not conjugate transposition) is what the real-linear swap implements. |
| 7 | `PaperSmallSideGram` provides conjugateTranspose measurability | **Pinned**, but explicitly **NO** `sourceGaussianmaplaw` for it. Candidate A correctly avoids this. |
| 8 | Tall prelog theorem already proved for arbitrary fixed mean | **Assumed from context** ("existing actual iid... ElogdetGram"). |

### Critical Risks

**Risk 1: Conflating transpose with conjugate-transpose.**
The candidate writes "$(X^T)^* X^T = XX^H$" — let's check: if we mean conjugate-transpose of $X^T$, that's $(X^T)^H = \bar{X}$. Then $(X^T)^H (X^T) = \bar{X} X^T$. This is NOT $XX^H$ in general. 

However, the candidate doesn't actually need this. They need Sylvester directly:
$$\det(I_N + \rho X^H X) = \det(I_m + \rho X X^H)$$
which is `Matrix.det_one_add_mul_comm` with appropriate substitutions. **If the candidate sticks to Sylvester and never writes down a spurious Gram-transpose identity, this risk is avoided.**

**Risk 2: The offset term changes meaning.**
For tall ($m \geq N$): offset = $\mathbb{E}[\log\det(X^H X)]$ where $X^H X$ is $N \times N$ full-rank a.s.
For wide ($m < N$): offset = $\mathbb{E}[\log\det(XX^H)]$ where $XX^H$ is $m \times m$ full-rank a.s.

Sylvester gives equality of $\det(I + \rho \cdot \text{Gram})$, so the *prelog* transfers. But does the **offset** transfer? At $\rho \to \infty$ asymptotics:
$$\log\det(I_N + \rho X^H X) = N\log\rho + \log\det(X^H X) + o(1) \quad \text{(tall)}$$
$$\log\det(I_m + \rho XX^H) = m\log\rho + \log\det(XX^H) + o(1) \quad \text{(wide)}$$

Since these are equal by Sylvester, and $m < N$... **contradiction?** No! They're equal as functions of $\rho$, so the leading terms must match. Indeed for wide $X$, $X^H X$ is singular (rank $m$), so $\det(X^H X) = 0$ and the expansion isn't valid that way. You MUST use the $XX^H$ form. The equality via Sylvester means:
$$\log\det(I_N + \rho X^H X) = \log\det(I_m + \rho XX^H)$$
and the RHS has leading term $m \log \rho + \log\det(XX^H)$. So the prelog is $m$ and the offset is $\mathbb{E}[\log\det(XX^H)]$. **This is consistent and correct.**

**Risk 3: Noncentral mean doesn't break anything.**
The arbitrary fixed mean $M$ becomes $M^T$ after transpose. The tall theorem must hold for arbitrary fixed mean (including $M^T$). Since the existing result states "arbitraryfixedmean M", this is satisfied. No issue.

---

## Comparison with Candidates B and C

| Aspect | Candidate A (Transpose) | Candidate B (Adjoint Real Isometry) | Candidate C (SVD/Spectral) |
|--------|------------------------|-------------------------------------|---------------------------|
| **Core map** | $X \mapsto X^T$ (real-linear swap) | $X \mapsto X^H$ (needs extra imaginary sign flip) | Zero-pad singular values |
| **Isometry available?** | Yes, pinned asset | Would need to construct; extra conjugation map | Needs spectral API |
| **Mean transform** | $M \mapsto M^T$ (clean) | $M \mapsto M^H$ (natural but harder to implement) | Unclear |
| **Gaussian preservation** | Direct from pinned assets | Extra sign map risks breaking standard structure | N/A without spectral tools |
| **API dependencies** | Sylvester + transpose reindex (both exist) | Conjugate isometry (not pinned, risk of inventing) | Spectral decomposition (explicitly excluded) |
| **Offset handling** | Automatic via Sylvester equality | Same | Must manually relate $\det(X^HX)$ zeros to $\det(XX^H)$ |
| **Verdict** | **Minimal obligations, all met** | Higher obligation, no source law for conj-transpose | Fictitious API risk |

Candidate B's problem: `PaperSmallSideGram` has conjugateTranspose measurability but **no** `sourceGaussianmaplaw`. Building an adjoint isometry requires composing transpose with entrywise conjugation. The conjugation map on the real source flips the sign of every imaginary coordinate—it's still an isometry, so it should preserve Gaussian. But the candidate would need to prove this composition exists as a measurable equiv and that `stdGaussian_map` applies. This is doable but **exceeds the pinned assets** and risks "inventing" infrastructure the prompt forbids.

Candidate C is dead on arrival per the constraint "no fictitious APIs."

---

## Numerical Controls (Seed 2026101924, 200k samples, 3 wide shapes)

These validate but don't prove. Key checks:

1. **Sylvester large/small/transposed determinant**: Verify $\det(I_N + \rho X^H X) = \det(I_m + \rho XX^H)$ numerically for wide shapes. Should hold to machine precision. Confirms the algebraic identity is being applied correctly.

2. **Noncentral trace and scalar Gamma digamma**: Cross-check the offset against known results. For central case ($M=0$), $\mathbb{E}[\log\det(XX^H)] = \sum_{k=0}^{m-1} \psi(N-k)$ where $\psi$ is digamma (for complex Wishart). For noncentral, verify against trace expansions.

3. **Wrong $N$ prelog negative control**: Fit the slope of $\mathbb{E}[C(\rho)]$ vs $\log\rho$ for wide matrices. Must get $m$, not $N$. If you get $N$, the code is incorrectly using the singular Gram.

---

## Verdict

**Candidate A is sound and minimal.** Its obligations are exactly the pinned assets plus Sylvester (available). The key insight is that you never need to manipulate the Gram matrix directly—you use Sylvester to equate the determinants, then use the transpose reindex isometry to transfer the expectation from wide to tall.

**One mandatory discipline**: Never write "$(X^T)^H X^T = XX^H$" or similar. Use only:
$$\det(I_N + \rho X^H X) = \det(I_m + \rho XX^H) \quad \text{(Sylvester, direct)}$$

The mean $M^T$ is a feature, not a bug—it correctly tracks that transposition (not conjugation) is the operative isometry. The tall theorem's "arbitrary fixed mean" hypothesis absorbs this.

No coding theorem, no SNR-varying mean, no spectral machinery. Just Sylvester + isometry + existing tall result. This is the right route.
