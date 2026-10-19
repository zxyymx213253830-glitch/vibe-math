# P4 Concrete Review: Actual Trace Variance Theorems

## Summary
These two files establish exact closed-form second moments for the trace of noncentral complex Wishart matrices via polynomial transport. Six theorems print with real Lean exit 0, using only standard axioms (classical choice, propext, funext). All shapes m,n including zeros; any fixed complex M; variance-one CN realized as real-paired/sqrt2. No full-rank, density, or premoment assumptions.

---

## File 1: ComplexGaussianTotalEnergyMoment.lean

**Three theorems — pure algebraic moment transport**

### Theorem 1: `complexGaussianPolynomialMoment_shifted_energy_pair`
Exact pair moment for shifted fourth Wick structure:
$$E[(Z_a+\mu_a)(\bar{Z}_a+\bar{\mu}_a)(Z_b+\mu_b)(\bar{Z}_b+\bar{\mu}_b)] = (1+|\mu_a|^2)(1+|\mu_b|^2) + \delta_{ab}(1+2|\mu_a|^2)$$

**Concrete verification:**
- **Diagonal (a=b):** $(1+|\mu_a|^2)^2 + (1+2|\mu_a|^2) = 2 + 4|\mu_a|^2 + |\mu_a|^4$. Matches shifted fourth moment of single CN variable.
- **Off-diagonal (a≠b):** Product $(1+|\mu_a|^2)(1+|\mu_b|^2)$. Independence confirmed.
- **Double-pair multiplicity:** The $\delta_{ab}$ coefficient is exactly 1, not 2. Correct because Wick pairing of 4 variables yields 3 pairings, but shifted structure absorbs one into mean.
- **Zero shape:** Empty index → sum vanishes, no impossible index call.

Relies on previously kernel-checked `complexGaussianPolynomialMoment_shifted_fourth`. L is linear, eval is ring hom.

### Theorem 2: `complexGaussianPolynomialMoment_total_energy_sq`
Sums pair theorem over all a,b:
$$E[(\text{total energy})^2] = T^2 + |\iota| + 2F$$
where $T = |\iota| + F$, $F = \sum_a |\mu_a|^2$.

**Concrete verification:**
- Diagonal contributes: $\sum_a [(1+|\mu_a|^2)^2 + (1+2|\mu_a|^2)]$
- Off-diagonal contributes: $\sum_{a \neq b} (1+|\mu_a|^2)(1+|\mu_b|^2)$
- Total: $(\sum_a(1+|\mu_a|^2))^2 + \sum_a(1+2|\mu_a|^2) = T^2 + |\iota| + 2F$ ✓
- **Coefficient check:** Variance = $|\iota| + 2F$, not $2(|\iota|+2F)$. Distinguishes from second spectral moment.

### Definition: `complexTotalEnergyPolynomial`
$\sum_a (X_{inl(a)} + \mu_a)(X_{inr(a)} + \bar{\mu}_a)$. Generic total energy polynomial, reused below.

---

## File 2: ActualGaussianTraceVariance.lean

**Four theorems — integral transport and centering**

### Theorem 3: `complexTotalEnergyPolynomial_eq_Gram_trace`
Algebraic identity: total energy polynomial = trace of Gram entry polynomial. Direct Finset manipulation, holds for all m,n including zeros.

### Theorem 4: `eval_complexTotalEnergyPolynomial_sq`
Evaluation commutes with squaring: polynomial evaluated at Gaussian sample equals $(\text{tr}((Z+M)^H(Z+M)))^2$. Uses `eval_noncentralGramEntryPolynomial` transport.

### Theorem 5: `integral_actualNoncentralGram_trace_sq_closed`
**Central result.** Transports Theorem 2 through integral:
$$\int \left(\text{Re tr}(W)\right)^2 d\gamma = T^2 + mn + 2F$$
where $W = (Z+M)^H(Z+M)$, $T = mn + F$, $F = \sum_{i,j}\|M_{ij}\|^2$.

**Concrete verification:**
- **PSD trace imaginary part zero:** `complexGram_posSemidef` ensures trace is real-nonneg, so `.re` extraction is lossless. Explicitly checked via `RCLike.nonneg_iff`.
- **Real/complex transfer:** `integral_re` applied to integrable polynomial. No divergent Bochner fiction—Gaussian mass 1, L1 integral reused.
- **Distinction from $E[\text{tr}(W^2)]$:** Previously proved $E[\text{tr}(W^2)] = mn(m+n) + 2(m+n)F + \text{tr}((M^HM)^2)$. Different object: that's trace of matrix square, this is square of scalar trace.
- **Empty shapes:** m=0 or n=0 → both sides equal 0. No division by empty index.
- **Coefficient sanity:** Variance term $mn + 2F$ has coefficient 1 on $mn$, not 2. Real DOF count: mn complex entries = 2mn real DOF, but variance-one CN normalization gives factor 1.

### Theorem 6: `integral_actualNoncentralGram_trace_centered_sq`
Centered variance:
$$\int (\text{Re tr}(W) - T)^2 d\gamma = mn + 2F$$

**Concrete verification:**
- Expansion: $E[(\text{tr} W)^2] - 2T \cdot E[\text{tr} W] + T^2 = (T^2 + mn + 2F) - 2T^2 + T^2 = mn + 2F$ ✓
- Uses previously proved mean: `actualExpectedGramPower_eq_closed M` giving $E[\text{tr} W] = T$.
- Integrability: `integrable_actualNoncentralGram_trace` and `_sq` already established. No new assumptions.
- **Centering validity:** Subtracting constant inside integral justified by `integral_add`, `integral_sub`, `integral_const_mul` with explicit integrability proofs.

---

## Cross-Cutting Checks

| Issue | Status |
|-------|--------|
| Exact coefficient: variance vs second spectral moment | Verified distinct: $mn+2F$ vs $mn(m+n)+...$ |
| Double-pair multiplicity | δ coefficient = 1, correct for shifted Wick |
| Real/complex transfer | `.re` extraction lossless via PSD; `integral_re` valid |
| Centering | Algebraically exact, integrability pre-proved |
| Zero shapes | All sums/powers defined, empty = 0 |
| Axioms | classical, propext, funext only |
| L linearity / ring hom | Used in `simp [hL]`, no re-derivation |
| Numerical SE controls | 200k samples, 5 shapes, central+noncentral PASS (prior) |

---

## Required Human Review Items

1. **Measure-theoretic transport:** Confirm `integral_actualComplexMatrix_polynomial` correctly identifies Lebesgue integral with polynomial moment functional (no hidden absolute convergence gap).
2. **Fubini justification:** Verify `integrable_actualNoncentralGram_trace_sq` establishes true L1 condition before applying `integral_add`/`integral_sub` in Theorem 6.
3. **Variance interpretation:** Confirm $mn + 2F$ matches theoretical prediction for trace-variance of noncentral Wishart (not conflated with Frobenius norm variance).
4. **Model review:** Validate that `stdGaussian _` on `ComplexSample` correctly implements variance-one CN via real-paired/sqrt2 construction.

All proofs Codex-generated. Human measure-theory/Fubini/variance/model review required. P4 is not human-verified nor independently compiled.
