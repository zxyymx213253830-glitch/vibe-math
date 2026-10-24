## P4 Adversarial Review: `OriginalCentralTwoByTwoT3.lean`

**Scope**: Hardcoded central 2×2, p=2, n=0, m=2, empty spectrum. Not a general T3 claim. All proof bodies are Codex-generated. Pinned Lean checks exit 0 on standard axioms; this review targets only logical/mathematical gaps in the explicit claims.

---

### Problem 1: Complex-to-Real Coercion Consistency (Mathematical)

In `theorem3CentralTwoSquare_candidate_eq_closed`, the RHS is cast from `ℝ` to `ℂ` via `(((x^2+2)*Real.exp (-x)-2*Real.exp (-2*x) : ℝ) : ℂ)`. The LHS (`theorem3IncrementCandidate ...`) must therefore produce a value whose imaginary part is provably zero for all `x ≥ 0`. The proof uses `push_cast` and `norm_num` after substituting real-valued determinant identities, but **no explicit lemma is invoked guaranteeing that `theorem3IncrementCandidate` itself is real-valued** under these parameters. This works only if every intermediate complex coercion cancels exactly—which `ring` can handle syntactically, but semantically relies on `theorem1PsiMatrix`, `theorem2XiMatrix`, and their determinants being real for real `x`. This is plausible given the hardcoded central instance but should be flagged: if any upstream definition introduces a stray `Complex.I`, the `push_cast; ring` step silently absorbs it without a reality check.

**Severity**: Low-medium. Likely closed by definitional unfolding of the specific 2×2 central case, but not explicitly verified here.

---

### Problem 2: `actualCentralTwoByTwo_T3Increment_closed` Returns `ℂ` with `.toReal` (Mathematical)

In `theorem3CentralTwoSquare_candidate_eq_actual_crossing`, the rewrite uses `(centralTwoByTwoT3Increment x).toReal`. This presupposes `centralTwoByTwoT3Increment x` is already known to be real (or that taking `.toReal` is the intended projection). However, the previous theorem (`_eq_closed`) established equality with a value coerced *into* `ℂ`. Chaining these:

```
candidate = (real_expr : ℂ)
candidate = (complex_increment).toReal : ℂ
```

This forces `(real_expr : ℂ) = ((complex_increment).toReal : ℂ)`, which implies the imaginary part of `centralTwoByTwoT3Increment x` is zero. **No lemma is cited proving `centralTwoByTwoT3Increment x ∈ ℝ`** for `x ≥ 0`. If it isn't, `.toReal` discards information and the equality holds trivially only because both sides project identically—not because the original complex values match.

**Severity**: Medium. A genuine semantic gap unless `centralTwoByTwoT3Increment` carries its own reality proof upstream.

---

### Problem 3: Recurrence Theorem Uses `.re` Projection (Mathematical)

`theorem3CentralTwoSquare_original_recurrence` states:

```
cdf1 = cdf2 + (increment_candidate).re
```

After rewriting the candidate to a real-coerced-to-complex expression, `simp only [Complex.ofReal_re]` extracts the real part. This is correct *if* the prior theorems hold. But this makes the recurrence relation contingent on both Problems 1 and 2 resolving cleanly. Any unreality in the increment propagates silently through `.re`.

**Severity**: Inherits from 1–2.

---

### Problem 4: No Positivity/Non-Degeneracy Check on `x = 0` Boundary (Minor)

All theorems assume `hx : 0 ≤ x`. At `x = 0`, the closed form evaluates to `((0+2)*1 - 2*1 : ℝ) = 0`, and determinants of row-mixed matrices at `x=0` should vanish. The proofs use `theorem1CentralTwoRow_PsiDet 0 (by norm_num)` which must handle `x=0` as a special case or uniformly. Not a gap per se, but worth confirming the upstream lemmas don't require `0 < x`.

**Severity**: Low.

---

**Summary**: Two concrete mathematical concerns—(1) implicit reality of the candidate without an explicit lemma, (2) `.toReal` projection equated against a `: ℂ` coercion without proving the source is real. Both are likely resolvable from upstream definitions in this hardcoded instance but represent actual logical dependencies not discharged within this file.
