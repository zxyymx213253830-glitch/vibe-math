# P1 Route Review: Affine Master Lemma for Complex Linear Gaussian Factorial Functional

## Setup Recap

We have `L : MvPolynomial (I ⊕ I, ℂ) →ₗ[ℂ] ℂ` satisfying:
- **Linearity** (given, do NOT assume multiplicativity)
- **Centered 4th moment**: `L(D(a)*D(b)*K(c)*K(d)) = (a·c)*(b·d) + (a·d)*(b·c)` where `a·c = Σ aᵢcᵢ`
- **2nd moment**: `L(X(inl i) * X(inr j)) = δᵢⱼ`
- **Charge balance**: monomials with unequal D/K count vanish
- **Coordinate shifted 4th theorem**: available (handles shifts by constants in the polynomial ring)

**Target**: For constants α,β,γ,δ ∈ ℂ and coefficient vectors a,b,c,d ∈ (I → ℂ):
```
L((D(a)+C*α)*(D(b)+C*β)*(K(c)+C*γ)*(K(d)+C*δ)) 
= αβγδ + βδ(a·c) + βγ(a·d) + αδ(b·c) + αγ(b·d) + (a·c)(b·d) + (a·d)(b·c)
```

**Critical convention**: c,d are already coefficients of K-variables. Do NOT conjugate. The dot products `a·c = Σ aᵢcᵢ` are bilinear over ℂ, not sesquilinear.

---

## Three Genuinely Different Routes

### Route A: Direct Multilinear Expansion + Charge Annihilation

**Idea**: Expand the product `(D(a)+α)(D(b)+β)(K(c)+γ)(K(d)+δ)` into 16 terms. Use charge-balance to kill 10 of them immediately. Evaluate the surviving 6 using lower-moment lemmas.

**Expansion structure** (grouping by D-count / K-count):
| Term | D-power | K-power | Charge balanced? | Contribution |
|------|---------|---------|------------------|--------------|
| αβγδ | 0 | 0 | Yes | αβγδ · L(1) |
| αβγ K(d) | 0 | 1 | No | 0 |
| αβδ K(c) | 0 | 1 | No | 0 |
| αγδ D(b) | 1 | 0 | No | 0 |
| βγδ D(a) | 1 | 0 | No | 0 |
| αβ K(c)K(d) | 0 | 2 | No | 0 |
| γδ D(a)D(b) | 2 | 0 | No | 0 |
| αγ D(b)K(d) | 1 | 1 | **Yes** | αγ · L(D(b)K(d)) |
| αδ D(b)K(c) | 1 | 1 | **Yes** | αδ · L(D(b)K(c)) |
| βγ D(a)K(d) | 1 | 1 | **Yes** | βγ · L(D(a)K(d)) |
| βδ D(a)K(c) | 1 | 1 | **Yes** | βδ · L(D(a)K(c)) |
| α D(b)K(c)K(d) | 1 | 2 | No | 0 |
| β D(a)K(c)K(d) | 1 | 2 | No | 0 |
| γ D(a)D(b)K(d) | 2 | 1 | No | 0 |
| δ D(a)D(b)K(c) | 2 | 1 | No | 0 |
| D(a)D(b)K(c)K(d) | 2 | 2 | **Yes** | L(D(a)D(b)K(c)K(d)) |

Surviving terms: 1 (degree 0) + 4 (degree 2) + 1 (degree 4) = 6 terms.

**Lower-moment lemmas needed**:
1. `L(1) = 1` (normalization — must be established or assumed)
2. `L(D(x) * K(y)) = x·y` for any coefficient vectors x,y

**Pros**: Completely elementary, no induction, no coordinate choices.  
**Cons**: Requires manually expanding a 4-fold product and tracking 16 terms; tedious but mechanical in Lean.

---

### Route B: Iterated Conditioning via Coordinate Shifted 4th Theorem

**Idea**: Treat the affine shift as a substitution `D(a) ↦ D(a) + α`, etc. Apply the coordinate shifted 4th theorem directly, which should state that for any constants s,t,u,v:

```
L((D(a)+s)(D(b)+t)(K(c)+u)(K(d)+v))
```
expands according to the known centered moments plus correction terms involving the shifts.

**Mechanism**: The coordinate shifted 4th theorem presumably gives exactly the expansion we need, provided we identify:
- The "centered" variables as D(a), D(b), K(c), K(d)
- The shifts as α, β, γ, δ

**Lower-moment lemmas needed**:
1. The coordinate shifted 4th theorem itself (already stated as available)
2. `L(D(x)) = 0`, `L(K(x)) = 0` (first moments vanish — follows from charge balance)
3. `L(D(x)*K(y)) = x·y` (second mixed moment)
4. `L(1) = 1`

**Pros**: One-shot application of an existing theorem; minimal manual expansion.  
**Cons**: Depends on the exact statement of the coordinate shifted 4th theorem being strong enough; if it only handles specific shift patterns, may not directly apply.

---

### Route C: Polarization / Finite-Difference Reduction

**Idea**: Recover the affine identity from the centered one by polarization. Define:
```
F(s,t,u,v) = L((D(a)+s)(D(b)+t)(K(c)+u)(K(d)+v))
```
This is a polynomial in s,t,u,v of degree ≤ 1 in each variable separately (since L is linear and the product expands multilinearly). Determine F by its values at enough points using finite differences.

Specifically:
- `F(0,0,0,0) = L(D(a)D(b)K(c)K(d)) = (a·c)(b·d) + (a·d)(b·c)` (centered 4th moment)
- `∂F/∂s|₀ = L(D(b)K(c)K(d))`... but wait, this has charge imbalance (1 D, 2 K), so = 0
- Mixed partials like `∂²F/∂s∂t|₀ = L(K(c)K(d))` = 0 (charge imbalance: 0 D, 2 K)
- `∂²F/∂s∂u|₀ = L(D(b)K(d)) = b·d`

By evaluating all mixed partials at 0 (each reduces to a lower moment that either vanishes by charge or equals a dot product), we reconstruct the full polynomial.

**Lower-moment lemmas needed**:
1. All charge-imbalanced moments vanish (given)
2. `L(D(x)K(y)) = x·y`
3. `L(1) = 1`
4. Multilinear reconstruction principle: a polynomial of degree ≤1 in each of 4 variables is determined by its 2⁴ = 16 evaluations (or equivalently by its mixed partials at 0)

**Pros**: Conceptually clean; avoids brute-force expansion; leverages multilinearity structurally.  
**Cons**: Requires setting up the polarization/finite-difference machinery in Lean; may be overkill for a single lemma.

---

## Lower-Moment Lemmas Required (All Routes)

| Lemma | Statement | Source |
|-------|-----------|--------|
| **L_one** | `L(1) = 1` | Must prove or assume as normalization axiom |
| **L_D_first** | `L(D(a)) = 0` | Charge balance (1≠0) |
| **L_K_first** | `L(K(c)) = 0` | Charge balance (0≠1) |
| **L_mixed_2** | `L(D(a) * K(c)) = a·c = Σ aᵢcᵢ` | From coordinate 2nd moment + linearity |
| **L_pure_2** | `L(D(a) * D(b)) = 0`, `L(K(c)*K(d)) = 0` | Charge balance |
| **L_centered_4** | Given | Hypothesis |

**Derivation of L_mixed_2**: From `L(X(inl i) * X(inr j)) = δᵢⱼ`, by linearity:
```
L(D(a)*K(c)) = L((Σ aᵢ X(inl i))(Σ cⱼ X(inr j))) = Σᵢⱼ aᵢcⱼ δᵢⱼ = Σ aᵢcᵢ
```
No conjugation on c. This is immediate.

**L_one**: If not already proved, note that `L` applied to the empty product (constant polynomial 1) must equal 1 for the target formula to hold at α=β=γ=δ=0, a=b=c=d=0. Likely needs to be an axiom or derived from `L` being a "functional" with `L(1)=1`.

---

## Best Lean-Friendly Approach

**Recommendation: Route A (Direct Expansion)**

Reasons:
1. **No infrastructure overhead**: Routes B and C require either invoking a possibly-restricted shifted theorem or building polarization machinery. Route A uses only `ring_nf` + rewriting by known lemmas.
2. **Tactic-friendly**: The 16-term expansion can be generated by `simp [add_mul, mul_add]` or `ring_nf`. Then filter terms using `simp only [charge_imbalance_lemmas]` to zero out 10 terms. The remaining 6 rewrite directly.
3. **Empty-type safe**: When `I = Empty`, all sums `Σ aᵢcᵢ` are empty sums = 0, and `D(a) = 0`, `K(c) = 0` as polynomials. The expansion still works: only the constant term `αβγδ · L(1)` survives, matching the RHS since all dot products are 0.
4. **No general APIs invented**: Works purely with the given hypotheses.

**Lean sketch**:
```lean
lemma affine_master {I : Type*} [Fintype I] (L : MvPolynomial (I ⊕ I) ℂ →ₗ[ℂ] ℂ)
  (hL_one : L 1 = 1)
  (hL_2 : ∀ (a c : I → ℂ), L (D a * K c) = ∑ i, a i * c i)
  (hL_4 : ∀ (a b c d : I → ℂ), L (D a * D b * K c * K d) = 
    (∑ i, a i * c i) * (∑ j, b j * d j) + (∑ i, a i * d i) * (∑ j, b j * c j))
  (hL_charge : ∀ m, ¬ charge_balanced m → L m = 0)
  (a b c d : I → ℂ) (α β γ δ : ℂ) :
  L ((D a + C α) * (D b + C β) * (K c + C γ) * (K d + C δ)) = 
    α*β*γ*δ + β*δ*(∑ i, a i*c i) + β*γ*(∑ i, a i*d i) + 
    α*δ*(∑ i, b i*c i) + α*γ*(∑ i, b i*d i) + 
    (∑ i, a i*c i)*(∑ j, b j*d j) + (∑ i, a i*d i)*(∑ j, b j*c j) := by
  -- Step 1: expand product
  simp only [add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm]
  -- Step 2: map L over sum (linearity)
  simp only [map_add, map_mul_C_left, map_mul_C_right] -- adjust for actual API
  -- Step 3: kill charge-imbalanced terms
  simp only [hL_charge, hL_D_first, hL_K_first, ...]
  -- Step 4: rewrite surviving terms using hL_2, hL_4, hL_one
  simp only [hL_2, hL_4, hL_one]
  -- Step 5: ring
  ring
```

---

## Empty-Type Pitfalls (`I = Empty`)

When `I = Empty`:

1. **Vectors `a,b,c,d : Empty → ℂ`** are unique (empty function). All sums `∑ i : Empty, _` evaluate to 0. So `D(a) = 0`, `K(c) = 0` as polynomials.

2. **MvPolynomial (Empty ⊕ Empty) ℂ ≃ ℂ** — the polynomial ring collapses to just constants. Every polynomial is a scalar.

3. **L becomes a linear map ℂ →ₗ[ℂ] ℂ**, which is multiplication by some constant. `hL_one` forces `L = id`.

4. **Target formula reduces to**: `L(αβγδ) = αβγδ`. All dot-product terms are 0. This holds iff `L(1) = 1`.

5. **Pitfall**: If `hL_one` is not available as a hypothesis, the lemma is unprovable for empty I. Also, any proof that pattern-matches on elements of I (e.g., "pick i : I") will fail vacuously — ensure all arguments use sums or universal quantifiers that degenerate correctly.

6. **Fintype.empty** instance exists in Mathlib, so `[Fintype I]` is satisfiable when `I = Empty`. No issue there.

7. **Charge balance for constants**: The constant polynomial 1 has 0 D's and 0 K's, so charge-balanced (0=0). Must not be killed by `hL_charge`.

---

## Next Application: Actual X = ZB + M

**Setup**: 
- Z is m×p random matrix, B is p×n deterministic, X = ZB + M (M deterministic mean)
- Covariance Σ = BᴴB (n×n, possibly singular if p < n or rank(B) < n)
- Want to apply the affine master lemma to functionals of X

**Key observations for P1 planning**:

1. **No invertibility of Σ**: The master lemma never divides by covariance entries. Dot products `a·c = Σ aᵢcᵢ` are purely algebraic. Singularity of BᴴB is irrelevant at this stage.

2. **Rectangular/singular B**: The index type I for the polynomial ring corresponds to column indices of X (size n). The D and K variables represent linear forms in X's columns. B enters only through how D(a) decomposes into Z-coordinates: `D_X(a) = D_Z(B*a)` where `B*a : Fin p → ℂ`. This is well-defined regardless of rank.

3. **Affine shift from M**: `X = ZB + M` means `D_X(a) = D_{ZB}(a) + C*(M·a)`. The constant `α = M·a = Σ Mᵢⱼ aⱼ` (appropriate contraction). This is exactly the affine form the master lemma handles.

4. **L multiplicative NOT assumed**: We never write `L(f*g) = L(f)*L(g)`. Linearity suffices because the master lemma's proof only uses `map_add` and scalar extraction.

5. **Numeric rational complex controls 0..4**: These likely refer to checking specific small instances (e.g., n ∈ {0,1,2,3,4}) as sanity tests before the general argument. The master lemma's proof is uniform in |I|, so these checks are validation, not part of the proof.

6. **API discipline**: Only use `D`, `K`, `L`, `MvPolynomial`, `map_add`, `map_smul`, the given moment hypotheses, and `Finset.sum`. Do not introduce Gaussian measures, characteristic functions, or Wick/Isserlis by name unless they appear in the existing development.

**Dependency chain for application**:
```
affine_master_lemma
  ↓
instantiate α = (M row contracted with a), etc.
  ↓  
rewrite D_X(a) = D_Z(Ba) + C*α
  ↓
apply affine_master to Z-functionals with vectors Ba, Bb, c, d
  ↓
dot products become (Ba)·c = a·(Bᴴc)... wait, NO conjugation convention check needed
```

**Convention check**: Since c,d are coefficients of K (conjugate) variables and we do NOT conjugate them, the dot product `(Ba)·c = Σⱼ (Ba)ⱼ cⱼ = Σⱼ (Σₖ Bⱼₖ aₖ) cⱼ`. This is bilinear. If later Σ = BᴴB appears, it comes from `Σₖ B̄ₖᵢ Bₖⱼ` which involves conjugating the first factor of Bᴴ, not our c vectors. Keep these separate.
