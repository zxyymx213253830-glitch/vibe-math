# P4 Independent Issues-Only Review: Codex Proof Author

## Scope
Reviewing only the two provided files: `FiniteSubsetPairGrouping.lean` (generic pair-of-subsets cardinality grouping) and `TwoExtraRowsGroupedPolynomial.lean` (rewriting the actual central (n+2)-by-n minimum polynomial). Controls n=0..8 are acknowledged as verification, not proof. No general spectral G2 or original T1 determinant equality claims in scope.

---

## Concrete Mathematical Issues Found

### Issue 1: Missing Nonemptiness Guard in `finsetPartitionEquiv_inter_card`

**Location:** `FiniteSubsetPairGrouping.lean`, theorem `finsetPartitionEquiv_inter_card`

**Problem:** The classical proof uses `a.property hs` to derive `False` when `a : {i // i ∉ S}` but `hs : a.val ∈ S`. This is correct. However, the forward direction of the `ext i` proof has:
```
obtain ⟨a,ha,he⟩ := Finset.mem_map.mp (Finset.mem_inter.mp hi).2
rcases a with a | a
· exact Finset.mem_map.mpr ⟨a,by simpa using ha,he⟩
· change a.val=i at he
  have hs : a.val ∈ S := he.symm ▸ (Finset.mem_inter.mp hi).1
  exact False.elim (a.property hs)
```
The case split `rcases a with a | a` is over `Sum α β` from `finsetCongr`. The second case maps `a : {i // i ∉ S}` back through the equivalence. The substitution `change a.val = i at he` followed by `he.symm ▸ ...` is **definitionally fragile**: if `he` is not definitionally `a.val = i` but only propositionally equal via the embedding, the rewrite may silently fail or require additional coherence. No explicit check ensures the embedding `(Equiv.sumCompl ...).toEmbedding` acts as `Sum.inl`/`Sum.inr` on elements rather than merely on membership proofs.

**Severity:** Medium. Likely works by definitional reduction in Lean 4's current kernel, but the proof body is not robust against changes in how `Equiv.finsetCongr` or `Finset.disjSum` compute their underlying maps. A `dsimp [finsetPartitionEquiv, Equiv.finsetCongr]` before the case split would make the computational behavior explicit.

---

### Issue 2: Implicit Cast Coherence in `sum_finsets_intersection_card`

**Location:** `FiniteSubsetPairGrouping.lean`, theorem `sum_finsets_intersection_card`, final `ring` call

**Problem:** The statement casts binomial coefficients to `ℝ`:
```lean
(S.card.choose c : ℝ) * ((n-S.card).choose b : ℝ) * f (c+b) c
```
but `f : ℕ → ℕ → ℝ` already returns `ℝ`. The intermediate sums after `Equiv.sum_comp` and `simp_rw` involve `Fintype.card_coe` rewrites. The `ring` tactic at the end must unify:
- `(a.choose c : ℝ)` from the LHS (after `hC` rewrite)
- `(S.card.choose c : ℝ)` from the RHS

These are equal because `a` is bound to `S.card` via `Fintype.card_coe` (`Fintype.card S = S.card`). However, **`ring` does not perform cardinality simplification**. The proof relies on `simp only [Fintype.card_coe]` having already replaced all `Fintype.card` instances with `Finset.card` before `ring` is called. If any residual `Fintype.card` term remains (e.g., from a subtype whose cardinality is not definitionally `n - S.card`), `ring` will see unmatched variables and the proof will fail or silently assume equality.

**Check:** The line `simp only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]` should reduce everything. But `Fintype.card_subtype_compl` gives `Fintype.card {i // i ∉ S} = Fintype.card (Fin n) - Fintype.card S`, which then needs `Fintype.card_fin` to become `n - S.card`. This chain is **order-dependent in `simp`**, and `simp only` with these three lemmas may not fire in the correct sequence without `simp_all` or explicit `rw`.

**Severity:** Low-Medium. Works in current Mathlib because `simp only` applies lemmas left-to-right repeatedly, but fragile if lemma statements change.

---

### Issue 3: `centralMixedMinorMoment_eq_byCards` Assumes `finiteMinorOverlap_left_card` / `right_card` Without Range Guards

**Location:** `TwoExtraRowsGroupedPolynomial.lean`, theorem `centralMixedMinorMoment_eq_byCards`

**Problem:** The proof begins:
```lean
have hs := finiteMinorOverlap_left_card S T
have ht := finiteMinorOverlap_right_card S T
```
These are imported from `RectangularWishartTwoExtraRows`. The theorem statement has **no hypothesis** that `S` and `T` satisfy the overlap conditions required by those lemmas (e.g., `S ⊆ Finset.univ`, `T ⊆ Finset.univ`, or cardinality bounds ensuring `t - S.card ≥ 0`). The `omega` calls later:
```lean
rw [show t-(S ∩ T).card-(S \ T).card=t-S.card by omega, ...]
```
will succeed only if the natural number subtractions do not underflow. But `t : ℕ` is a free parameter with no constraint `t ≥ S.card` or `t ≥ (S ∩ T).card + (S \ T).card`.

If `t < S.card`, then `t - S.card = 0` in `ℕ` (truncated subtraction), while `t - (S ∩ T).card - (S \ T).card` also truncates, potentially to a **different** value if the intermediate subtraction order differs. The `omega` tactic proves equalities in `ℤ` and back-casts, but it **cannot guard against truncated subtraction divergence** unless premises ensure non-underflow.

**Severity:** High. The theorem as stated is only valid when `t ≥ S.card` and `t ≥ T.card`. Without these guards (or importing them from the `finiteMinorOverlap` lemmas' own preconditions), the `omega` rewrites are unsound for small `t`. The controls n=0..8 may hide this if the test range never triggers underflow for the specific `t = n` instantiation used downstream, but the **general theorem over arbitrary `t`** is unguarded.

**Fix Required:** Add hypotheses `(htS : S.card ≤ t) (htT : T.card ≤ t)` or restrict `t := n` before the `omega` calls.

---

### Issue 4: Multiplicity Formula Domain Mismatch Between Files

**Location:** `FiniteSubsetPairGrouping.lean` theorem `sum_finsets_pair_cardinalities` vs. `TwoExtraRowsGroupedPolynomial.lean` definition `twoExtraRowGroupedPolynomial`

**Problem:** The grouping theorem produces multiplicity:
```
(n.choose a) * (a.choose c) * ((n-a).choose b)
```
where per the user's specification: `a = |S|`, `c = |S ∩ T|`, `b = |T \ S|`, so `|T| = c + b`.

The polynomial definition uses:
```lean
centralMixedMinorMomentByCards n a (c+b) c 1 1
```
which matches `t=n`, first arg=`a=|S|`, second arg=`c+b=|T|`, third arg=`c=|S∩T|`.

However, `centralMixedMinorMomentByCards` is defined as:
```lean
def centralMixedMinorMomentByCards (t a b c p q : ℕ) : ℝ :=
  centralDeterminantPowerMoment (t-c) c (p+q) *
    (centralDeterminantPowerMoment (t-a) (a-c) p *
      centralDeterminantPowerMoment (t-b) (b-c) q)
```
Here `b` in the def is `|T| = c+b` from the grouping. So the third factor is `centralDeterminantPowerMoment (t-(c+b)) ((c+b)-c) q = centralDeterminantPowerMoment (t-c-b) b q`. This requires `t ≥ c + b` and `b ≤ t - c` for the moment indices to be valid (non-negative).

The summation range `b ∈ Finset.range (n-a+1)` ensures `b ≤ n - a`, and since `a ≥ c`, we get `c + b ≤ c + (n-a) ≤ n = t`. So the bound holds. **But**: the second factor uses `(t-a)` and `(a-c)`, requiring `t ≥ a` and `a ≥ c`. The range `c ∈ Finset.range (a+1)` gives `c ≤ a ✓`. The range `a ∈ Finset.range (n+1)` gives `a ≤ n = t ✓`.

**No issue here.** Bounds are coherent. Documenting for completeness; the finite partition equivalence correctly transfers to the moment index domain.

---

### Issue 5: `actualTwoExtraRows_covariance_minimum_CDF_grouped` Scaling Law Application

**Location:** `TwoExtraRowsGroupedPolynomial.lean`, final theorem

**Problem:** The proof is:
```lean
rw [actualTwoExtraRows_covariance_minimum_CDF n hn v hv x hx,
  twoExtraRowMinimumPolynomial_eq_grouped]
```
This assumes `actualTwoExtraRows_covariance_minimum_CDF` already expresses the CDF in terms of `twoExtraRowMinimumPolynomial n (x/v)`. The rewrite replaces that polynomial with the grouped version. 

**Risk:** If the imported covariance theorem has the form `1 - exp(-n*x/v) * twoExtraRowMinimumPolynomial n (x/v)` but the scaling inside the exponential differs (e.g., `exp(-n*(x/v))` vs `exp(-(n*x)/v)`), the `rw` will fail to match. In `ℝ` these are equal, but **syntactic matching in `rw` is not semantic**. The current statement shows `Real.exp (-(n : ℝ)*(x/v))` which parses as `exp(-(n*(x/v)))`, matching `exp(-n*x/v)` by associativity. This should work, but only if the imported theorem uses exactly this parenthesization.

**Severity:** Low. Syntactic, not mathematical. Would surface immediately as a `rw` failure, not a silent error.

---

## Summary of Concrete Issues

| # | Severity | Location | Issue |
|---|----------|----------|-------|
| 1 | Medium | `finsetPartitionEquiv_inter_card` | Definitional fragility in embedding computation; no `dsimp` guard |
| 2 | Low-Med | `sum_finsets_intersection_card` | `simp only` lemma ordering dependence for cardinality reduction before `ring` |
| 3 | **High** | `centralMixedMinorMoment_eq_byCards` | Missing `t ≥ S.card` / `t ≥ T.card` guards; `omega` unsound under truncated subtraction |
| 4 | None | Multiplicity formula | Verified coherent; documenting for audit trail |
| 5 | Low | Covariance CDF grouped | Syntactic `rw` matching risk on exponential parenthesization |

**Issue 3 is the only mathematically concrete defect** that could produce a false theorem statement. It requires either adding hypotheses or restricting the quantification over `t`.
