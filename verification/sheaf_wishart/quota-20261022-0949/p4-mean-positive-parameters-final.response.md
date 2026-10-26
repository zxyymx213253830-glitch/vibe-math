## P4 Adversarial Review: MeanPositiveNoncentrality.lean

**1. Index coercion ill-typed in definition (Mathematical Gap)**

In `meanPositiveNoncentrality`, the index passed to `eigenvalues₀` is:
```lean
Fin.cast (Fintype.card_fin n).symm (Fin.castLE (Matrix.rank_le_width M) i)
```
where `i : Fin M.rank`. The term `Fin.castLE (Matrix.rank_le_width M) i` produces a term of type `Fin n` (since `M.rank ≤ n`). However, `Fin.cast (Fintype.card_fin n).symm` expects an input of type `Fin (Fintype.card (Fin n))`, which is definitionally `Fin n` but the cast direction is inverted: `(Fintype.card_fin n).symm` has type `n = Fintype.card (Fin n)`, so `Fin.cast` along `.symm` maps `Fin n → Fin (Fintype.card (Fin n))`. This is a roundabout identity, but the real issue is that `eigenvalues₀` expects an index in `Fin (Fintype.card (Fin n))` while the semantic intent is to index into the positive eigenvalues. If `eigenvalues₀` is defined on `Fin (Fintype.card α)` for the matrix type, this works; if it expects `Fin n` directly, the outer cast is type-correct but semantically suspicious—verify the exact signature of `eigenvalues₀` against what `complexGram_posSemidef` returns.

**2. `antitone_positive_iff_lt_count` application missing argument (Potential Gap)**

In `meanPositiveNoncentrality_pos`:
```lean
apply (antitone_positive_iff_lt_count _
  (complexGram_posSemidef M).1.eigenvalues₀_antitone _).mpr
```
The lemma `antitone_positive_iff_lt_count` likely requires a proof that the eigenvalue sequence is antitone and nonneg, plus an index bound. The second `_` is a placeholder for a proof that the count of strictly positive values equals `M.rank` (supplied by the subsequent `rw [gram_positive_modes_card_eq_rank]`). However, the `.mpr` direction yields `0 < eigenvalues₀ i` from `i < count`. The goal is `0 < meanPositiveNoncentrality M i`, which unfolds correctly, but **the proof does not explicitly discharge that `eigenvalues₀` is nonnegative**—this is buried in the antitone+count lemma's hypotheses. If that lemma requires a separate nonnegativity proof not inferable from context, this is incomplete.

**3. StrictAnti hypothesis unused except in packaging (Minor)**

In `exists_paper_positiveNoncentralSpectrum_of_strict`, `hs : StrictAnti (meanPositiveNoncentrality M)` is passed directly into the structure. Correct, but note: `StrictAnti` on `Fin M.rank → ℝ` combined with positivity forces `M.rank ≥ 1` implicitly (otherwise the type is empty and strictness is vacuous). If downstream consumers assume nonemptiness, this should be documented.

**4. `funext` + `convert` congruence fragility (API Question)**

In the final theorem, after `convert hParams ⟨i.val,hm⟩ using 1 <;> congr 1`, the two `congr 1` goals must resolve the `Fin.cast` coercion equality between `M` and `N` parameter indices. This relies on `hRank : M.rank = N.rank` making `Fin.cast hRank` definitionally compatible with the `⟨i.val, hm⟩` / `⟨i.val, hn⟩` pair. If `Fin.cast` does not reduce definitionally here, `congr 1` may leave dangling coercion-equality subgoals. **This is not a mathematical gap** but a potential Lean elaboration failure requiring `simp [Fin.ext_iff]` or similar.

**5. No measure-theoretic side conditions verified**

`actualNoncentral_paperJointSpectrum_law_of_positive_parameters` equates pushforward measures under `paperJointSpectrum M` and `N`. The proof delegates entirely to `actualNoncentral_paperJointSpectrum_law_of_meanGram_eigenvalues`. If that imported lemma requires measurability of `paperJointSpectrum` or absolute continuity conditions not stated here, they are inherited assumptions. Not a gap in *this* file, but a dependency risk.
