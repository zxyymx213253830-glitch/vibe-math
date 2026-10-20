# P4 Issues-Only Review: `localcorrelated-fourth-3`

## Concrete Issues

### 1. Critical: Incorrect cross-term indices in moment formula vs. weighted Wick law

The stated physical law is:
$$L((D_a+C_\alpha)(D_b+C_\beta)(K_c+C_\gamma)(K_d+C_\delta)) = \alpha\beta\gamma\delta + \beta\delta\langle a,c\rangle + \beta\gamma\langle a,d\rangle + \alpha\delta\langle b,c\rangle + \alpha\gamma\langle b,d\rangle + \langle a,c\rangle\langle b,d\rangle + \langle a,d\rangle\langle b,c\rangle$$

Mapping the theorem's arguments to `complexGaussianPolynomialMoment_weighted_shifted_fourth a b c d α β γ δ`:
- `a = row_k(B_{·j})`, `b = row_l(B_{·v})`, `c = row_k(conj(B_{·i}))`, `d = row_l(conj(B_{·u}))`
- `α = M_{kj}`, `β = M_{lv}`, `γ = conj(M_{ki})`, `δ = conj(M_{lu})`

**Issue**: The inner products must match the weighted Wick formula exactly:
- `⟨a,c⟩ = Σ_t a(t)·c(t) = Σ_t B_{tj}·conj(B_{ti}) = (B^H B)_{ij} = complexGram B i j` ✓
- `⟨a,d⟩ = Σ_t B_{tj}·conj(B_{tu}) = (B^H B)_{uj} = complexGram B u j` 
- `⟨b,c⟩ = Σ_t B_{tv}·conj(B_{ti}) = (B^H B)_{iv} = complexGram B i v`
- `⟨b,d⟩ = Σ_t B_{tv}·conj(B_{tu}) = (B^H B)_{uv} = complexGram B u v` ✓

Checking the cross terms in the theorem against the law's `βδ⟨a,c⟩ + βγ⟨a,d⟩ + αδ⟨b,c⟩ + αγ⟨b,d⟩`:

| Law term | Expected | Theorem has | Match? |
|----------|----------|-------------|--------|
| `βδ⟨a,c⟩` | `M_{lv}·conj(M_{lu})·Gram_{ij}` | `complexGram B i j * star(M l u) * M l v` | ✓ |
| `βγ⟨a,d⟩` | `M_{lv}·conj(M_{ki})·Gram_{uj}` | `(if k=l)·complexGram B u j·star(M k i)·M l v` | **See #2** |
| `αδ⟨b,c⟩` | `M_{kj}·conj(M_{lu})·Gram_{iv}` | `(if k=l)·complexGram B i v·M k j·star(M l u)` | **See #2** |
| `αγ⟨b,d⟩` | `M_{kj}·conj(M_{ki})·Gram_{uv}` | `complexGram B u v * star(M k i) * M k j` | ✓ |

### 2. Critical: Missing indicator on `⟨a,d⟩` and `⟨b,c⟩` terms when k≠l

From `complexRowCoefficient_pair`:
- `⟨a,d⟩ = Σ_t row_k(B_{·j})(t) · row_l(conj(B_{·u}))(t) = if k=l then Gram_{uj} else 0`
- `⟨b,c⟩ = Σ_t row_l(B_{·v})(t) · row_k(conj(B_{·i}))(t) = if k=l then Gram_{iv} else 0`

The theorem correctly includes `(if k=l then 1 else 0)` factors on these terms. **No issue here** — this is correct. The `complexRowCoefficient_gram` theorem already handles this, and the proof uses it properly.

### 3. Moderate: Commutativity reordering in `he` may not hold for `MvPolynomial`

```lean
have he : correlatedConjugateEntryPolynomial ... * correlatedDirectEntryPolynomial ... =
          correlatedDirectEntryPolynomial ... * correlatedDirectEntryPolynomial ... *
          correlatedConjugateEntryPolynomial ... * correlatedConjugateEntryPolynomial ... := by ring
```

`MvPolynomial` over `ℂ` is commutative, so `ring` should discharge this. However, the specific polynomial type `ComplexMatrixPolynomial m p` must have a `CommRing` instance for `ring` to work. If it only has `Ring`, this will fail silently or produce incorrect results. **Verify that `ComplexMatrixPolynomial m p` is definitionally a commutative ring** (it should be as `MvPolynomial` over a commutative base).

### 4. Minor: Proof fragility in `complexRowCoefficient_gram`

```lean
rw [complexRowCoefficient_pair]
split_ifs <;> simp [complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply,mul_comm]
```

When `k ≠ l`, the LHS is 0 and RHS is 0 by the `if`. When `k = l`, you need `Σ_b B_{bj} · conj(B_{bi}) = (B^H B)_{ij}`. The `simp` with `mul_comm` suggests potential orientation issues between `Matrix.mul_apply` (which gives `Σ_k A_{ik} B_{kj}`) and `complexGram`'s definition. **Confirm that `complexGram B i j` is defined as `Σ_b conj(B_{bi}) · B_{bj}` (= `(B^H B)_{ij}`)** and that `mul_comm` bridges the order difference in the summand.

### 5. Style/Clarity: Conjugation placement inconsistency

In `correlatedConjugateEntryPolynomial`, you write `star (B b i)` inside `complexRowCoefficient` but `star (M k i)` as the constant. This is mathematically correct (conjugating the entire linear functional's coefficient), but consider documenting why the `star` on `B` appears inside the row coefficient rather than outside the polynomial constructor, for auditability.

---

## Summary of Required Actions

| Priority | Issue | Action |
|----------|-------|--------|
| **P4-Critical** | None found — the formula matches the weighted Wick law after careful index tracing | — |
| **P4-Moderate** | #3 `ring` on `ComplexMatrixPolynomial` | Confirm `CommRing` instance exists/is imported |
| **P4-Minor** | #4 `complexGram` orientation | Verify definition matches `Σ_b conj(B_{bi})·B_{bj}` |

**Bottom line**: After tracing all indices through the weighted Wick mapping, the theorem statement appears **correct**. The cross terms, indicators, and Gram matrix indices align with the physical law `αβγδ + βδ·ac + βγ·ad + αδ·bc + αγ·bd + ac·bd + ad·bc`. No unjustified rank/inverse/density assumptions are present. The main verification burden is on the `CommRing` instance for the polynomial type and the `complexGram` definition orientation.
