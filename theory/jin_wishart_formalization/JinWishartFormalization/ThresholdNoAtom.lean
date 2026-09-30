import JinWishartFormalization.ComplexGramSimpleSpectrum
import JinWishartFormalization.GramSpectrumTransfer
import JinWishartFormalization.WeylComplexHermitian
import JinWishartFormalization.PaperStatements

/-!
# No threshold atoms for the paper's ordered eigenvalues (card G2b)

For every rectangular shape `m × n`, every deterministic complex mean `M` and
every fixed real threshold `x`, no ordered eigenvalue of the paper's
smaller-side Gram matrix equals `x`, almost surely:

* `x` is an eigenvalue iff the characteristic polynomial vanishes at `x`;
  evaluated through the generic sample, this is one polynomial `P_x` in the
  `2mn` real sample coordinates;
* the scaled embedding witness mean `a·E` (Gram `a² I`, with `a² = |x| + 1`)
  shows `P_x ≠ 0`;
* `sampleEval_ne_zero_ae` (null zero set, translation, Gaussian absolute
  continuity) finishes.

Combined with the simple-spectrum theorem this makes the actual model an
instance of `Paper.OrderedEigenvalueLaw`, and the paper's event recurrence (22)
holds on the actual model with **no** atom hypothesis left
(`paperModel_kthCDFRecurrence_strict`).
-/

open Matrix Polynomial MeasureTheory ProbabilityTheory

namespace JinWishart

noncomputable section

variable {m n : ℕ}

/-! ### Threshold polynomial -/

/-- The generic row / column Gram characteristic polynomial evaluated at `x`. -/
def genericRowGramCharpolyAt (m n : ℕ) (x : ℝ) : MvPolynomial (SampleIdx m n) ℂ :=
  (genericComplexRowGram m n).charpoly.eval (MvPolynomial.C (x : ℂ))

def genericGramCharpolyAt (m n : ℕ) (x : ℝ) : MvPolynomial (SampleIdx m n) ℂ :=
  (genericComplexGram m n).charpoly.eval (MvPolynomial.C (x : ℂ))

private theorem sampleEval_charpolyAt {d : ℕ}
    (G : Matrix (Fin d) (Fin d) (MvPolynomial (SampleIdx m n) ℂ))
    (z : ComplexSample (m := m) (n := n)) (x : ℝ) :
    sampleEval z (G.charpoly.eval (MvPolynomial.C (x : ℂ))) =
      (G.map (sampleEval z)).charpoly.eval (x : ℂ) := by
  rw [charpoly_map, Polynomial.eval_map]
  have hC : sampleEval z (MvPolynomial.C (x : ℂ)) = (x : ℂ) := by
    simp [sampleEval]
  rw [← hC, Polynomial.eval₂_at_apply, hC]

theorem genericRowGramCharpolyAt_eval (z : ComplexSample (m := m) (n := n)) (x : ℝ) :
    sampleEval z (genericRowGramCharpolyAt m n x) =
      (complexSampleMatrix z * (complexSampleMatrix z)ᴴ).charpoly.eval (x : ℂ) := by
  rw [genericRowGramCharpolyAt, sampleEval_charpolyAt, genericComplexRowGram_map]

theorem genericGramCharpolyAt_eval (z : ComplexSample (m := m) (n := n)) (x : ℝ) :
    sampleEval z (genericGramCharpolyAt m n x) =
      (complexGram (complexSampleMatrix z)).charpoly.eval (x : ℂ) := by
  rw [genericGramCharpolyAt, sampleEval_charpolyAt, genericComplexGram_map]

/-! ### Scaled embedding witnesses -/

/-- Column witness (`n ≤ m`): the scalar `a` on the embedded diagonal. -/
def scaledColumnWitness (hnm : n ≤ m) (a : ℝ) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => if i = Fin.castLE hnm j then (a : ℂ) else 0

/-- Row witness (`m ≤ n`). -/
def scaledRowWitness (hmn : m ≤ n) (a : ℝ) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => if j = Fin.castLE hmn i then (a : ℂ) else 0

theorem complexGram_scaledColumnWitness (hnm : n ≤ m) (a : ℝ) :
    complexGram (scaledColumnWitness hnm a) = diagonal (fun _ : Fin n => ((a ^ 2 : ℝ) : ℂ)) := by
  ext j k
  simp only [complexGram, Matrix.mul_apply, Matrix.conjTranspose_apply, scaledColumnWitness,
    Matrix.diagonal_apply]
  by_cases hjk : j = k
  · subst hjk
    simp [apply_ite star, ite_mul, Finset.sum_ite_eq', sq]
  · have hne : Fin.castLE hnm j ≠ Fin.castLE hnm k := fun h =>
      hjk (Fin.castLE_injective hnm h)
    simp only [hjk, ite_false]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hij : i = Fin.castLE hnm j
    · subst hij
      simp [hne]
    · simp [hij]

theorem rowGram_scaledRowWitness (hmn : m ≤ n) (a : ℝ) :
    scaledRowWitness hmn a * (scaledRowWitness hmn a)ᴴ =
      diagonal (fun _ : Fin m => ((a ^ 2 : ℝ) : ℂ)) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, scaledRowWitness,
    Matrix.diagonal_apply]
  by_cases hik : i = k
  · subst hik
    simp [apply_ite star, mul_ite, Finset.sum_ite_eq', sq]
  · have hne : Fin.castLE hmn i ≠ Fin.castLE hmn k := fun h =>
      hik (Fin.castLE_injective hmn h)
    simp only [hik, ite_false]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j = Fin.castLE hmn i
    · subst hji
      simp [hne.symm, hik]
    · simp [hji]

/-- The witness scale: `a² = |x| + 1 ≠ x`. -/
private def witnessScale (x : ℝ) : ℝ := Real.sqrt (|x| + 1)

private theorem witnessScale_sq (x : ℝ) : witnessScale x ^ 2 = |x| + 1 :=
  Real.sq_sqrt (by positivity)

private theorem diag_const_charpoly_eval_ne_zero (d : ℕ) (x : ℝ) :
    (diagonal (fun _ : Fin d => ((witnessScale x ^ 2 : ℝ) : ℂ))).charpoly.eval (x : ℂ) ≠ 0 := by
  rw [Matrix.charpoly_diagonal, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [sub_ne_zero, witnessScale_sq]
  intro h
  have hR : x = |x| + 1 := by exact_mod_cast h
  have := le_abs_self x
  linarith

theorem genericRowGramCharpolyAt_ne_zero (hmn : m ≤ n) (x : ℝ) :
    genericRowGramCharpolyAt m n x ≠ 0 := by
  intro hzero
  have key := genericRowGramCharpolyAt_eval
    (complexSampleMean (scaledRowWitness hmn (witnessScale x))) x
  rw [hzero, map_zero, complexSampleMatrix_complexSampleMean,
    rowGram_scaledRowWitness] at key
  exact diag_const_charpoly_eval_ne_zero m x key.symm

theorem genericGramCharpolyAt_ne_zero (hnm : n ≤ m) (x : ℝ) :
    genericGramCharpolyAt m n x ≠ 0 := by
  intro hzero
  have key := genericGramCharpolyAt_eval
    (complexSampleMean (scaledColumnWitness hnm (witnessScale x))) x
  rw [hzero, map_zero, complexSampleMatrix_complexSampleMean,
    complexGram_scaledColumnWitness] at key
  exact diag_const_charpoly_eval_ne_zero n x key.symm

/-! ### From a nonvanishing charpoly to "no eigenvalue equals `x`" -/

theorem hermitian_eigenvalues₀_ne_of_charpoly_eval_ne_zero {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) {x : ℝ}
    (h : A.charpoly.eval (x : ℂ) ≠ 0) (i : Fin (Fintype.card (Fin d))) :
    hA.eigenvalues₀ i ≠ x := by
  intro hix
  apply h
  rw [hA.charpoly_eq, Polynomial.eval_prod]
  let e : Fin (Fintype.card (Fin d)) ≃ Fin d := Fintype.equivOfCardEq (Fintype.card_fin _)
  apply Finset.prod_eq_zero (Finset.mem_univ (e i))
  have hev : hA.eigenvalues (e i) = hA.eigenvalues₀ i := by
    simp only [Matrix.IsHermitian.eigenvalues]
    congr 1
    simp [e]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hev, hix]
  exact sub_self _

/-- **No threshold atoms.** For every fixed real `x`, almost surely no ordered
eigenvalue of the paper's smaller-side Gram matrix equals `x`. -/
theorem paperSmallSideGram_eigenvalues_ne_threshold_ae
    (M : Matrix (Fin m) (Fin n) ℂ) (x : ℝ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      ∀ i, (paperSmallSideGram_posSemidef (complexSampleMatrix z + M)).1.eigenvalues₀ i ≠ x := by
  classical
  by_cases hmn : m ≤ n
  · filter_upwards [sampleEval_ne_zero_ae (genericRowGramCharpolyAt_ne_zero hmn x) M]
      with z hz i
    apply hermitian_eigenvalues₀_ne_of_charpoly_eval_ne_zero
    rw [genericRowGramCharpolyAt_eval, complexSampleMatrix_add_mean] at hz
    have hcp : (paperSmallSideGram (complexSampleMatrix z + M)).charpoly =
        ((complexSampleMatrix z + M) * (complexSampleMatrix z + M)ᴴ).charpoly := by
      unfold paperSmallSideGram
      rw [dite_cond_eq_true (eq_true hmn)]
      exact charpoly_submatrix_equiv _ _
    rw [hcp]
    exact hz
  · have hnm : n ≤ m := le_of_not_ge hmn
    filter_upwards [sampleEval_ne_zero_ae (genericGramCharpolyAt_ne_zero hnm x) M]
      with z hz i
    apply hermitian_eigenvalues₀_ne_of_charpoly_eval_ne_zero
    rw [genericGramCharpolyAt_eval, complexSampleMatrix_add_mean] at hz
    have hcp : (paperSmallSideGram (complexSampleMatrix z + M)).charpoly =
        (complexGram (complexSampleMatrix z + M)).charpoly := by
      unfold paperSmallSideGram
      rw [dite_cond_eq_false (eq_false hmn)]
      exact charpoly_submatrix_equiv _ _
    rw [hcp]
    exact hz

/-! ### The actual model as a `Paper.OrderedEigenvalueLaw` -/

/-- Descending eigenvalues of the paper's small-side Gram, indexed by `Fin (min m n)`. -/
def paperModelEigenvalue (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (min m n))
    (z : ComplexSample (m := m) (n := n)) : ℝ :=
  (paperSmallSideGram_posSemidef (complexSampleMatrix z + M)).1.eigenvalues₀
    (Fin.cast (Fintype.card_fin (min m n)).symm i)

theorem measurable_paperModelEigenvalue (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (min m n)) :
    Measurable (paperModelEigenvalue M i) := by
  let G : ComplexSample (m := m) (n := n) → HermitianMatrix (min m n) := fun z =>
    ⟨paperSmallSideGram (complexSampleMatrix z + M),
      (paperSmallSideGram_posSemidef (complexSampleMatrix z + M)).1⟩
  have hG : Measurable G :=
    (measurable_shiftedPaperSmallSideGram M).subtype_mk
      (h := fun z => (paperSmallSideGram_posSemidef (complexSampleMatrix z + M)).1)
  change Measurable ((fun A : HermitianMatrix (min m n) =>
    hermitianEigenvalueVector A (Fin.cast (Fintype.card_fin (min m n)).symm i)) ∘ G)
  exact (orderedHermitianEigenvalueCoordinatesContinuous (min m n) _).measurable.comp hG

private theorem fin_cast_le {a b : ℕ} (h : a = b) {i j : Fin a} (hij : i ≤ j) :
    Fin.cast h i ≤ Fin.cast h j :=
  Fin.le_iff_val_le_val.mpr (by simpa using Fin.le_iff_val_le_val.mp hij)

private theorem fin_cast_injective {a b : ℕ} (h : a = b) :
    Function.Injective (Fin.cast h) := fun i j hij =>
  Fin.ext (by simpa using congrArg Fin.val hij)

/-- The actual shifted complex Gaussian model, with the paper's small-side
ordered spectrum, satisfies every field of `Paper.OrderedEigenvalueLaw`. -/
def paperModelLaw (M : Matrix (Fin m) (Fin n) ℂ) :
    Paper.OrderedEigenvalueLaw (ComplexSample (m := m) (n := n))
      (stdGaussian (ComplexSample (m := m) (n := n))) (min m n) where
  phi := paperModelEigenvalue M
  measurable := measurable_paperModelEigenvalue M
  ordered := fun z i j hij =>
    Matrix.IsHermitian.eigenvalues₀_antitone _ (fin_cast_le _ hij)
  strictAnti_ae := by
    filter_upwards [paperSmallSideGram_eigenvalues_injective_ae M] with z hz
    apply Antitone.strictAnti_of_injective
    · exact fun i j hij => Matrix.IsHermitian.eigenvalues₀_antitone _ (fin_cast_le _ hij)
    · exact hz.comp (fin_cast_injective _)
  nonneg := fun i z => by
    have hpsd := paperSmallSideGram_posSemidef (complexSampleMatrix z + M)
    let j : Fin (min m n) := Fintype.equivOfCardEq (Fintype.card_fin _)
      (Fin.cast (Fintype.card_fin (min m n)).symm i)
    have hj := hpsd.eigenvalues_nonneg j
    simpa [j, paperModelEigenvalue, Matrix.IsHermitian.eigenvalues] using hj

/-- Each ordered eigenvalue of the actual model has no atom at any threshold. -/
theorem paperModelEigenvalue_atom_eq_zero (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (min m n)) (x : ℝ) :
    stdGaussian (ComplexSample (m := m) (n := n)) {z | paperModelEigenvalue M i z = x} = 0 := by
  have h := paperSmallSideGram_eigenvalues_ne_threshold_ae M x
  rw [ae_iff] at h
  apply measure_mono_null _ h
  intro z hz
  simp only [Set.mem_ofPred_eq, not_forall, not_not]
  exact ⟨_, hz⟩

/-- **Paper equation (22) on the actual model, unconditionally.** For the
shifted complex Gaussian sample and `2 ≤ k ≤ s = min m n`,
`P(φ_k ≤ x) = P(φ_{k-1} ≤ x) + P(φ_k < x < φ_{k-1})`. The no-atom hypothesis of
`Paper.orderedEigenvalueLaw_kthCDFRecurrence_strict` is discharged by
`paperModelEigenvalue_atom_eq_zero`. -/
theorem paperModel_kthCDFRecurrence_strict (M : Matrix (Fin m) (Fin n) ℂ)
    (k : ℕ) (hk : 2 ≤ k) (hks : k ≤ min m n) (x : ℝ) :
    let law := paperModelLaw M
    stdGaussian (ComplexSample (m := m) (n := n))
        {z | Paper.OrderedEigenvalueLaw.kth law k (by omega) hks z ≤ x} =
      stdGaussian (ComplexSample (m := m) (n := n))
          {z | Paper.OrderedEigenvalueLaw.kth law (k - 1) (by omega) (by omega) z ≤ x} +
        stdGaussian (ComplexSample (m := m) (n := n))
          {z | Paper.OrderedEigenvalueLaw.kth law k (by omega) hks z < x ∧
            x < Paper.OrderedEigenvalueLaw.kth law (k - 1) (by omega) (by omega) z} := by
  intro law
  exact Paper.orderedEigenvalueLaw_kthCDFRecurrence_strict _ law k hk hks x
    (paperModelEigenvalue_atom_eq_zero M _ x)

end

end JinWishart
