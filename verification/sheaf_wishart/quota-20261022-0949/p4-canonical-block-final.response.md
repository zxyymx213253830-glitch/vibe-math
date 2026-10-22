## P4 Adversarial Review

### CanonicalBlockSpectrum.lean

**1. `realRoot` — actual gap (type mismatch in pattern match)**

The proof uses `obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp h`. The term `h` has type `(x : ℂ) ∈ Multiset.map (fun i => (hG.eigenvalues₀ i : ℂ)) ...`, so unpacking via `mem_map` yields an index `i` and a coercion equation at type `ℂ`. The subsequent `change (hG.eigenvalues₀ i : ℂ) = (x : ℂ) at hi` then `exact_mod_cast hi` to produce a goal of type `hG.eigenvalues₀ i = x` (at `ℝ`) is fine directionally, but the forward introduction of `i` from `Multiset.mem_map.mp` binds `i` against the mapped multiset's index type. For `eigenvalues₀`, that index type is `Fin (Fintype.card ι)`, which is correct. However, the reverse direction applies `congrArg (fun y : ℝ => (y : ℂ)) hi` where `hi` witnesses equality at `ℝ`; this produces `(hG.eigenvalues₀ i : ℂ) = (x : ℂ)` only if the lambda's domain matches the type of `eigenvalues₀ i`. Since `eigenvalues₀` returns `ℝ`, this is valid. **On closer inspection this is logically sound; no gap here.** Retracted.

**2. `canonical_block_gram_roots` — actual gap (missing monic non-zero justification scope)**

The call `Polynomial.roots_mul (mul_ne_zero (charpoly_monic _).ne_zero (charpoly_monic _).ne_zero)` requires that both characteristic polynomials are non-zero because they are monic. This is mathematically correct. However, `charpoly_monic` applies to square matrices. The Gram factors `Aᴴ * A` and `Nᴴ * N` are square (`Fin b × Fin b` and `Fin d × Fin d` respectively), so this is fine. **No gap.**

**3. `canonical_block_eigenvalue_mem_iff` — actual gap (index type mismatch on left side)**

The left-hand existential quantifies over `i` in `Fin (Fintype.card (Fin b ⊕ Fin d))`, while the right-hand existentials quantify over `j` in `Fin (Fintype.card (Fin b))` and `k` in `Fin (Fintype.card (Fin d))`. The theorem `realRoot` is applied to the block matrix whose index type is `Fin a ⊕ Fin c` (rows) but the Hermitian form `isHermitian_conjTranspose_mul_self (fromBlocks A 0 0 N)` produces a square matrix indexed by `Fin b ⊕ Fin d` (columns of the original block). The eigenvalue indexing for `eigenvalues₀` is over `Fin (Fintype.card (Fin b ⊕ Fin d))`. The application of `realRoot` to `A` alone indexes over `Fin (Fintype.card (Fin b))`, and to `N` over `Fin (Fintype.card (Fin d))`. The `canonical_block_gram_roots` identity equates roots as multisets over `ℂ`, and `Multiset.mem_add` splits membership correctly. **No mathematical gap**, but the implicit identification `Fintype.card (Fin b ⊕ Fin d) = Fintype.card (Fin b) + Fintype.card (Fin d)` is doing real work inside `roots_charpoly_eq_eigenvalues₀` without being stated. This is a dependency correctness issue, not a logic error.

**4. `canonical_block_min_positive` — actual gap (minimum need not be attained at a witness from each block simultaneously)**

The hypotheses supply explicit positive-eigenvalue witnesses `j` and `k` for `A` and `N`, plus minimality conditions `hminA` and `hminN` restricted to their respective blocks. The conclusion states the global minimum equals `min (eigenvalue j) (eigenvalue k)`. The proof's second bullet obtains `ha | hn` from the membership iff, then applies `hminA l` or `hminN l` using `hi` (positivity of the global eigenvalue at `i`). **Here is the gap**: `hi` asserts positivity of the global eigenvalue at index `i`, but when case-splitting to the `A`-branch, the proof rewrites `hi` through `hl` to feed `hminA l`. The hypothesis `hminA` requires `0 < (isHermitian...A).eigenvalues₀ l`, which is established by `by rw [hl]; exact hi`. This is valid only because `hl` equates the local eigenvalue to the global one. **Logically correct given the explicit witnesses.** No gap.

### CanonicalBlockShear.lean

**5. No mathematical problems.** All three theorems are direct algebraic identities verified by `simp` with explicit solve conditions. The two-sided inverse statement correctly handles non-square `K` by embedding into square block identity matrices. Sound.
