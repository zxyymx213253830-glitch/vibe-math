## Route Assessment

The proposed route is **sound and optimal** for the actual complex standard Gaussian. It cleanly separates algebraic cancellation from analytic integrability, avoiding any radial integral redo or unverified moment assumptions.

### Off-Diagonal (p ≠ q): Exact Zero via Rotation

The mechanism works perfectly for `μ = (stdGaussian ℂ).map (z ↦ (√2)⁻¹ • z)`:

1. **Unit choice**: `c = exp(iπ/(p-q))` has `‖c‖ = 1`
2. **Distributional invariance**: Since `μ` is rotationally invariant (inherited from `stdGaussian ℂ` via the existing `stdGaussian_map` LinearIsometryEquiv infrastructure), multiplication by `c` preserves `μ`
3. **Phase extraction**: `c^p * conj(c)^q = exp(iπ(p-q)/(p-q)) = exp(iπ) = -1`
4. **Self-cancellation**: `∫ z^p conj(z)^q dμ = ∫ (cz)^p conj(cz)^q dμ = c^p conj(c)^q ∫ z^p conj(z)^q dμ = -∫ z^p conj(z)^q dμ`
5. **Conclusion**: Integral equals its negative → exactly 0

**No desired moment assumption needed.** This is pure algebraic consequence of rotational symmetry.

### Diagonal (p = q): Gamma Moment Reduction

`∫ |z|^(2p) dμ` reduces via your existing assets:
- `‖z‖²/2` under `stdGaussian ℂ` has `Exp(1)` law (already proved)
- Scaling: if `w ~ μ`, then `‖w‖² = ‖(√2)⁻¹ z‖² = ‖z‖²/2 ~ Exp(1)`
- Therefore `∫ |w|^(2p) dμ = ∫ (‖z‖²/2)^p d(Exp(1)) = Γ(p+1) = p!`
- Uses your **already-proved integer Gamma moments** directly

---

## Minimal Prerequisites Identified

### Integrability (Bochner)

For universal polynomial moment evaluation, you need:

1. **Finite all norm powers**: `∀ n : ℕ, ∫⁻ z, ‖z‖^n ∂μ < ∞`
   - Follows from `Exp(1)` energy control: `∫ ‖z‖^(2k) dμ = k! < ∞`
   - Odd powers: `‖z‖^(2k+1) ≤ 1 + ‖z‖^(2k+2)` or Cauchy-Schwarz against even moments
   - This single fact unlocks Bochner integrability for all `z^p conj(z)^q` since `|z^p conj(z)^q| = ‖z‖^(p+q)`

2. **Product integrability**: `∫ |z^p conj(z)^q| dμ < ∞` for all `p,q`
   - Immediate from (1) with `n = p+q`

### Finite Product / MvPolynomial Infrastructure

For **universal** evaluation (arbitrary polynomials, not just monomials):

3. **Finite product decomposition**: Ability to express `∫ (Σᵢ aᵢ ∏ⱼ z^(pⱼ) conj(z)^(qⱼ)) dμ = Σᵢ aᵢ ∏ⱼ ∫ z^(pⱼ) conj(z)^(qⱼ) dμ`
   - Requires: finite sum commutes with integral (linearity) + **finite product of integrable functions is integrable**
   - Your existing "finite Pi/product transports already proved" likely covers this, but verify it handles *products of different monomials* (not just identical factors)

4. **MvPolynomial evaluation map** (unverified API name): A ring homomorphism from `MvPolynomial (Fin 2) ℂ` (variables representing `z`, `conj(z)`) into `L²(μ)` or the Bochner-integrable functions
   - Must respect: `eval₂ μ (X 0) = fun z ↦ z`, `eval₂ μ (X 1) = fun z ↦ conj z`
   - Well-definedness requires (1)–(3) above
   - The off-diagonal/diagonal split then becomes: `eval₂ μ P = Σ (monomial terms)`, each term evaluated by the route above

5. **Conjugate-linearity handling**: `conj(z)` is not holomorphic; ensure your polynomial framework treats `z` and `conj(z)` as *algebraically independent* variables over `ℂ` (real-linear but not complex-linear in the second slot)

### Numeric Validation Role

Your `fixedseed200000 p,q ∈ 0..4` and `Exp(1)` energy controls serve as **sanity checks**, not proof components. They confirm:
- The `√2` scaling is correctly applied (variance-one, not variance-two)
- No accidental real Wishart or real Gaussian formulas leaked in
- The phase cancellation isn't numerically masked by floating-point drift

---

## Summary

**Route verdict**: Proceed. The rotation trick gives exact off-diagonal zeros without integrability side conditions (once rotational invariance of `μ` is established via `stdGaussian_map`). The diagonal is a direct repackaging of your existing `Exp(1)` + Gamma moments.

**Bottleneck**: Item (3)—verify your finite product transport theorem handles mixed monomials `z^a conj(z)^b * z^c conj(z)^d`, not just powers of a single function. Everything else is already in your locked assets.
