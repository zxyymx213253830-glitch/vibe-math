# P1 Route Planning: Determinant Identity for H1 + xH0

## Setup
Target: `det(H1 + xH0) = (∏ i<n, i!(i+1)!) * ∑ k≤n, C(n,k)x^k/k!` for `Fin n` matrices with `H0_ij=(i+j)!`, `H1_ij=(i+j+1)!`.

---

## Route 1: J-Recurrence + Laguerre Coefficients

**Strategy:** Use `H1 = AJAᵀ` (J = diag(2i+1)) and `H0 = AAᵀ` to write `det(H1+xH0) = det(A)² · det(J+xI)`. Since `det(A)² = ∏(i!)²` is pinned, reduce to computing `det(J+xI)` and matching it to the Laguerre-type sum.

**Essential lemmas:**
1. `det(J + xI) = ∏_{i<n}(2i+1+x)` — diagonal determinant (trivial).
2. Coefficient identity: `∏_{i<n}(2i+1+x) = ∏(i+1)/∏(i!) · ∑ C(n,k)x^k/k!` — **this is false as stated**; the RHS is the target divided by `∏i!(i+1)!`, so the actual algebraic bridge between `∏(2i+1+x)` and `∑C(n,k)x^k/k!` requires a non-trivial polynomial identity relating rising-factorial products to partial exponential sums.
3. Boundary: n=0 gives det=1, sum=1. n=1 gives `(1+x)` vs `1+x` ✓.

**First step:** Verify symbolically that `∏_{i<n}(2i+1+x) · ∏_{i<n}i!(i+1)! = (∏ i<n, i!²) · ∑ C(n,k)x^k/k!` simplifies correctly. This reduces to checking `∏(2i+1+x) = ∑C(n,k)x^k/k! · ∏(i!/(i+1)!)`... which doesn't simplify cleanly.

**Risk:** The factorization `H1=AJAᵀ` is numerically verified but the route from `det(J+xI)` to the Laguerre sum may require an identity that doesn't exist in this form. **Fragility: HIGH** — the product-to-sum conversion is the entire difficulty and may not factor through J cleanly.

---

## Route 2: Christoffel Augmented Determinant

**Strategy:** Interpret `H0, H1` as moment matrices for the functional `F(X^k)=k!`. Then `H1+xH0` is the moment matrix of `(t+x)dμ`. Use the Christoffel-type formula: multiplying the measure by a degree-1 polynomial `(t+x)` modifies the determinant by a ratio expressible via orthogonal polynomials.

**Essential lemmas:**
1. Finite-difference orthogonality: construct monic polynomials `P_k` of degree k with `F(P_i P_j)=0` for `i≠j`, using the pinned basis-change asset.
2. Christoffel determinant shift: `det(M_n[(t+x)dμ]) = det(M_n[dμ]) · Q_n(x)` where `Q_n` is determined by the orthogonal polynomials evaluated at `-x`.
3. Identification: `Q_n(x) = ∑C(n,k)x^k/k!` via explicit signed construction (no Laguerre API; build directly from `F`).
4. Boundary: n=0 trivially; n=1 yields `F(t+x)=1+x` ✓.

**First step:** Construct the monic orthogonal polynomial `P_1(t) = t - F(t)/F(1) = t-1` using the pinned monic basis-change asset. Compute `F((t+x)·1)` and `F((t+x)·P_1)` to extract the n=2 augmented determinant explicitly.

**Risk:** Requires proving the Christoffel formula for finite Hankel-like determinants without a general spectral theorem. The "already proved CDF" asset provides the target polynomial but not the mechanism. **Fragility: MEDIUM** — conceptually clean but needs a finite-dimensional Christoffel lemma from scratch.

---

## Route 3: Direct Column Operations / Monic Rising Factorial Basis

**Strategy:** Apply the pinned "monic degree-preserving basis change preserves bilinear moment determinants" to transform columns of `H1+xH0` into a rising factorial basis where the matrix becomes triangular or has known determinant.

**Essential lemmas:**
1. Rising factorial basis `{t^(k̄) = t(t+1)...(t+k-1)}` satisfies `F(t^(k̄)) = k!·C(something)` — compute explicitly.
2. Column operations reducing `H1+xH0` to upper triangular form with diagonal entries yielding `∏i!(i+1)!` times the Laguerre sum coefficients.
3. The polynomial `∑C(n,k)x^k/k!` emerges as the determinant of the transformation matrix.
4. Boundary: n=0 empty product=1; n=1 direct computation `(1!+x·0!)=1+x` ✓.

**First step:** For n=2, write the 2×2 matrix `[(1+x)!, (2+x)!; (2+x)!, (3+x)!]`... wait, entries are `(i+j+1)! + x(i+j)!`. Perform explicit column subtraction `C_j ← C_j - (j+x)C_{j-1}` and verify the determinant factors.

**Risk:** Column operation patterns may not generalize uniformly across all n without an inductive invariant. **Fragility: LOW-MEDIUM** — most elementary, directly verifiable on Seed2026102403 controls.

---

## Comparison

| | Effort | Fragility | Key blocker |
|---|---|---|---|
| R1 | Low if identity holds | HIGH | Product-to-sum bridge unclear |
| R2 | Medium-High | MEDIUM | Finite Christoffel lemma needed |
| R3 | Medium | LOW-MED | Inductive pattern discovery |

**Critical warning:** Seed2026102403 passing for n=0..8 is **necessary but not sufficient**. Finite verification is not proof. A route that merely reproduces the n≤8 numerics without structural induction risks being a coincidence-fitting exercise. The smallest independently useful first step across all routes is **proving the n=1 and n=2 cases symbolically in Lean** (not numerically), establishing the base for induction.
