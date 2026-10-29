## P4 Adversarial Review: `MixedCoefficientMinorZero.lean`

**1. Missing injectivity hypothesis in `mixedCoefficient_ordered_det_pos`**

The theorem `mixedCoefficient_ordered_det_pos` assumes `hks : StrictMono k` but does not assume that the composite row selection `mixedOrderedSelection p L N hpN k` is injective. While `StrictMono k` ensures injectivity of `k` on `Fin L`, and `Fin.castLE hpN` is injective on `Fin p`, the theorem does not verify that their images are disjoint as a hypothesis—it derives disjointness from `hkp : ∀ i, p ≤ (k i).val` inside the proof of `mixedCoefficient_ordered_eq`. This is logically sufficient for the matrix equality, but the determinant positivity claim implicitly requires that the submatrix extraction preserves the non-degeneracy structure of `weightedGeneralizedConfluent`. If `weightedGeneralizedConfluent_det_pos` itself assumes injectivity of the index map `fun i => (k i).val`, then `hks` suffices; if it requires injectivity of the full row selector, this must be stated or derived. The current statement leaves this dependency implicit.

**2. Weight indexing domain mismatch in `hw` hypotheses**

In `mixedCoefficient_canonical_det_pos`, the hypothesis is `hw : ∀ i : Fin L, 0 < w (p + i.val)`. In `mixedCoefficient_ordered_det_pos`, it is `hw : ∀ i, 0 < w ((k i).val)`. These are passed to `weightedZeroConfluentVandermonde_det_pos` and `weightedGeneralizedConfluent_det_pos` respectively. However, `w : ℕ → ℝ` is defined on all naturals, and the theorems only constrain `w` at specific indices. There is no explicit assumption that these are the *only* weights that matter for the determinant, nor that `w` is nonnegative elsewhere. This is not a gap if the imported determinant positivity theorems have matching signatures, but the review flag `[需人工审查]` explicitly calls out finite selection indexing—confirming the exact weight-index requirements of the downstream theorems is necessary.

**3. `mixedCoefficientMinor_zero_of_repeated` uses extensional equality after `rw [hij]`**

The proof applies `Matrix.det_zero_of_row_eq hne` then uses `funext k` followed by `rw [hij]`. Since `hij : f i = f j`, rewriting replaces `f i` with `f j` in the goal, making both sides definitionally equal. This is correct but relies on `funext` over `Fin p ⊕ Fin L`, which introduces function extensionality as an axiom dependency. This is standard but worth noting for the axioms printout.

**4. No actual mathematical gaps detected**

All claims are algebraic identities or direct reductions to imported theorems. The zero-of-missing-column and zero-of-repeated-row arguments are structurally sound. The canonical and ordered equivalences are verified by `ext i j` case analysis with appropriate simplifications. Determinant positivity is delegated entirely to imported results with syntactically matching hypotheses. The `[需人工审查]` note concerns API-level indexing alignment, not logical validity.
