import JinWishartFormalization.WishartSimpleSpectrum
import JinWishartFormalization.GaussianRadialLaw
import JinWishartFormalization.WishartProbability
import JinWishartFormalization.PaperSmallSideGram
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Almost-sure simple spectrum of the shifted complex Gram sample, any dimension

For `n ≤ m`, the `n × n` Gram matrix `(X + M)ᴴ (X + M)` of an actual shifted
complex Gaussian `m × n` sample has pairwise distinct eigenvalues with
probability one, for every deterministic mean `M`.

Route (generalizing `ComplexGramTwoByTwoGaussianSimpleSpectrum` and the real
`WishartSimpleSpectrum`):

1. The Gram matrix of the *generic* complex sample is a matrix over the
   complex polynomial ring in the `2mn` real coordinates.  The resultant of
   its characteristic polynomial with the derivative is one polynomial
   `genericComplexGramResultant m n`; evaluating it at a real sample gives the
   resultant for that sample.
2. A Hermitian matrix whose charpoly/derivative resultant is nonzero has a
   separable characteristic polynomial, hence injective ordered eigenvalues.
3. A diagonal witness sample (possible because `n ≤ m`) shows the generic
   resultant is a nonzero polynomial.
4. A nonzero complex-coefficient polynomial vanishes only on a Lebesgue-null
   set of real points; translation and Gaussian absolute continuity finish.

The hypothesis `n ≤ m` is necessary: for `n ≥ m + 2` the matrix `XᴴX` has a
repeated zero eigenvalue for every sample.  The paper's smaller-side Gram
matrix always falls under this case after choosing the orientation.
-/

open Matrix Polynomial MeasureTheory ProbabilityTheory

namespace JinWishart

noncomputable section

/-! ### Complex-coefficient polynomials vanish on null sets of real points -/

/-- The real points where a nonzero complex polynomial vanishes form a null set. -/
theorem complex_polynomial_realZeroSet_volume_eq_zero (p : ℂ[X]) (hp : p ≠ 0) :
    volume {t : ℝ | p.eval (t : ℂ) = 0} = 0 := by
  have hfin : {z : ℂ | p.IsRoot z}.Finite := Polynomial.finite_setOfPred_isRoot hp
  have hcount : {t : ℝ | p.eval (t : ℂ) = 0}.Countable := by
    apply (hfin.countable.preimage Complex.ofReal_injective).mono
    intro t ht
    exact ht
  exact hcount.measure_zero volume

/-- A nonzero complex-coefficient polynomial in `n` variables vanishes only on a
Lebesgue-null set of real points.  Same induction as
`mvPolynomial_zeroSet_volume_eq_zero`, with complex coefficients. -/
theorem complexMvPolynomial_realZeroSet_volume_eq_zero_fin :
    ∀ n (p : MvPolynomial (Fin n) ℂ), p ≠ 0 →
      volume {x : Fin n → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) p = 0} = 0 := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have hconst : p = MvPolynomial.C (p.coeff 0) := MvPolynomial.eq_C_of_isEmpty p
      have hc : p.coeff 0 ≠ 0 := by
        intro hzero
        apply hp
        rw [hconst, hzero, MvPolynomial.C_0]
      have hset : {x : Fin 0 → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) p = 0} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rw [hconst, MvPolynomial.eval_C]
        exact hc
      rw [hset]
      simp
  | succ n ih =>
      intro p hp
      classical
      let q : Polynomial (MvPolynomial (Fin n) ℂ) := MvPolynomial.finSuccEquiv ℂ n p
      have hq : q ≠ 0 := by
        intro h
        exact hp ((MvPolynomial.finSuccEquiv ℂ n).injective h)
      let r : MvPolynomial (Fin n) ℂ := q.leadingCoeff
      have hr : r ≠ 0 := by
        intro h
        exact hq ((Polynomial.leadingCoeff_eq_zero).mp h)
      have hException :
          volume {y : Fin n → ℝ | MvPolynomial.eval (fun i => (y i : ℂ)) r = 0} = 0 :=
        ih r hr
      have hExceptionAE : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
          MvPolynomial.eval (fun i => (y i : ℂ)) r ≠ 0 := by
        simpa [ae_iff, Set.mem_ofPred_eq] using hException

      let e : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      let S : Set (ℝ × (Fin n → ℝ)) :=
        {z | MvPolynomial.eval
          (fun i => ((Fin.cons z.1 z.2 : Fin (n + 1) → ℝ) i : ℂ)) p = 0}
      have hS : MeasurableSet S := by
        have hcons : Continuous (fun z : ℝ × (Fin n → ℝ) =>
            (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ)) := by
          apply continuous_pi
          intro i
          refine Fin.cases ?_ ?_ i
          · exact continuous_fst
          · intro j
            exact (continuous_apply j).comp continuous_snd
        have hcomplex : Continuous (fun z : ℝ × (Fin n → ℝ) =>
            fun i => ((Fin.cons z.1 z.2 : Fin (n + 1) → ℝ) i : ℂ)) :=
          continuous_pi fun i =>
            Complex.continuous_ofReal.comp ((continuous_apply i).comp hcons)
        have heval : Continuous (fun z : ℝ × (Fin n → ℝ) =>
            MvPolynomial.eval
              (fun i => ((Fin.cons z.1 z.2 : Fin (n + 1) → ℝ) i : ℂ)) p) :=
          (MvPolynomial.continuous_eval p).comp hcomplex
        exact (isClosed_singleton.preimage heval).measurableSet

      have hpres : MeasurePreserving e :=
        MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have hpre : e ⁻¹' S =
          {x : Fin (n + 1) → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) p = 0} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, S]
        have hpoint :
            (Fin.cons (e x).1 (e x).2 : Fin (n + 1) → ℝ) = x := by
          funext i
          refine Fin.cases ?_ ?_ i
          · simp [e, MeasurableEquiv.piFinSuccAbove]
          · intro j
            rfl
        rw [hpoint]
      have hmeasure :
          volume {x : Fin (n + 1) → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) p = 0} =
            volume S := by
        rw [← hpre, ← hpres.map_eq]
        exact (e.map_apply S).symm

      have hqEval_ne (y : Fin n → ℝ) (hy : MvPolynomial.eval (fun i => (y i : ℂ)) r ≠ 0) :
          Polynomial.map (MvPolynomial.eval (fun i => (y i : ℂ))) q ≠ 0 := by
        intro hzero
        have hlead : (Polynomial.map (MvPolynomial.eval (fun i => (y i : ℂ))) q).leadingCoeff
            = 0 := by
          simp [hzero]
        have hlead' : (Polynomial.map (MvPolynomial.eval (fun i => (y i : ℂ))) q).leadingCoeff =
            MvPolynomial.eval (fun i => (y i : ℂ)) r := by
          rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hy]
        rw [hlead'] at hlead
        exact hy hlead

      have hFiber (y : Fin n → ℝ) (hy : MvPolynomial.eval (fun i => (y i : ℂ)) r ≠ 0) :
          volume {t : ℝ | MvPolynomial.eval
            (fun i => ((Fin.cons t y : Fin (n + 1) → ℝ) i : ℂ)) p = 0} = 0 := by
        have hfun (t : ℝ) : (fun i => ((Fin.cons t y : Fin (n + 1) → ℝ) i : ℂ)) =
            (Fin.cons (t : ℂ) (fun i => (y i : ℂ)) : Fin (n + 1) → ℂ) := by
          funext i
          refine Fin.cases ?_ ?_ i
          · simp
          · intro j
            simp
        have hset : {t : ℝ | MvPolynomial.eval
              (fun i => ((Fin.cons t y : Fin (n + 1) → ℝ) i : ℂ)) p = 0} =
            {t : ℝ | Polynomial.eval (t : ℂ)
              (Polynomial.map (MvPolynomial.eval (fun i => (y i : ℂ))) q) = 0} := by
          ext t
          simp only [Set.mem_ofPred_eq]
          rw [hfun t, MvPolynomial.eval_eq_eval_mv_eval']
        rw [hset]
        exact complex_polynomial_realZeroSet_volume_eq_zero _ (hqEval_ne y hy)

      have hFiberAE :
          (fun y : Fin n → ℝ => volume ((fun t : ℝ => (t, y)) ⁻¹' S)) =ᵐ[volume] 0 := by
        filter_upwards [hExceptionAE] with y hy
        simpa [S] using hFiber y hy

      have hSzero : volume S = 0 := by
        rw [Measure.volume_eq_prod ℝ (Fin n → ℝ), Measure.prod_apply_symm hS]
        exact lintegral_eq_zero_of_ae_eq_zero hFiberAE
      rw [hmeasure, hSzero]

/-- Index-type-free version: any finite index type. -/
theorem complexMvPolynomial_realZeroSet_volume_eq_zero {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℂ) (hp : p ≠ 0) :
    volume {x : ι → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) p = 0} = 0 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hq : MvPolynomial.rename e p ≠ 0 := by
    intro h
    apply hp
    apply MvPolynomial.rename_injective e e.injective
    simpa using h
  have hnull := complexMvPolynomial_realZeroSet_volume_eq_zero_fin _ _ hq
  let Φ : (ι → ℝ) ≃ᵐ (Fin (Fintype.card ι) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ => ℝ) e
  have hΦ : MeasurePreserving Φ volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ => ℝ) e
  have hpre : Φ ⁻¹' {y : Fin (Fintype.card ι) → ℝ |
      MvPolynomial.eval (fun i => (y i : ℂ)) (MvPolynomial.rename e p) = 0} =
      {x : ι → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) p = 0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, MvPolynomial.eval_rename]
    have hfun : ((fun i => ((Φ x i : ℝ) : ℂ)) ∘ e) = fun i => (x i : ℂ) := by
      funext i
      simp only [Function.comp_apply, Φ]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rw [hfun]
  rw [← hpre, hΦ.measure_preimage_equiv]
  exact hnull

/-! ### The generic complex Gram matrix -/

/-- Real coordinates of a complex `m × n` sample: `((row, column), re/im)`. -/
abbrev SampleIdx (m n : ℕ) := (Fin m × Fin n) × Fin 2

/-- The generic complex sample, entries `(x_re + i x_im) / √2`, over the complex
polynomial ring in the real coordinates. -/
def genericComplexSample (m n : ℕ) :
    Matrix (Fin m) (Fin n) (MvPolynomial (SampleIdx m n) ℂ) :=
  fun i j => (MvPolynomial.X ((i, j), 0) +
      MvPolynomial.C Complex.I * MvPolynomial.X ((i, j), 1)) *
    MvPolynomial.C ((Real.sqrt 2 : ℂ))⁻¹

/-- Conjugate transpose of the generic sample, written out entrywise (complex
conjugation is not a ring map on the polynomial ring). -/
def genericComplexSampleConjT (m n : ℕ) :
    Matrix (Fin n) (Fin m) (MvPolynomial (SampleIdx m n) ℂ) :=
  fun j i => (MvPolynomial.X ((i, j), 0) -
      MvPolynomial.C Complex.I * MvPolynomial.X ((i, j), 1)) *
    MvPolynomial.C ((Real.sqrt 2 : ℂ))⁻¹

/-- The generic column Gram matrix `XᴴX`. -/
def genericComplexGram (m n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (SampleIdx m n) ℂ) :=
  genericComplexSampleConjT m n * genericComplexSample m n

/-- Resultant of the generic Gram charpoly with its derivative. -/
def genericComplexGramResultant (m n : ℕ) : MvPolynomial (SampleIdx m n) ℂ :=
  resultant (genericComplexGram m n).charpoly
    (genericComplexGram m n).charpoly.derivative n (n - 1)

variable {m n : ℕ}

/-- Evaluation of coordinate polynomials at an actual real sample. -/
def sampleEval (z : ComplexSample (m := m) (n := n)) :
    MvPolynomial (SampleIdx m n) ℂ →+* ℂ :=
  MvPolynomial.eval (fun k => ((z k : ℝ) : ℂ))

theorem genericComplexSample_map (z : ComplexSample (m := m) (n := n)) :
    (genericComplexSample m n).map (sampleEval z) = complexSampleMatrix z := by
  ext i j
  simp [genericComplexSample, sampleEval, complexSampleMatrix, div_eq_mul_inv]

theorem genericComplexSampleConjT_map (z : ComplexSample (m := m) (n := n)) :
    (genericComplexSampleConjT m n).map (sampleEval z) = (complexSampleMatrix z)ᴴ := by
  ext j i
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, genericComplexSampleConjT,
    complexSampleMatrix, sampleEval]
  apply Complex.ext <;> simp [div_eq_mul_inv]

theorem genericComplexGram_map (z : ComplexSample (m := m) (n := n)) :
    (genericComplexGram m n).map (sampleEval z) = complexGram (complexSampleMatrix z) := by
  rw [genericComplexGram, Matrix.map_mul, genericComplexSampleConjT_map,
    genericComplexSample_map]
  rfl

/-- Evaluating the generic resultant at a sample gives the resultant of that
sample's Gram charpoly with its derivative. -/
theorem genericComplexGramResultant_eval (z : ComplexSample (m := m) (n := n)) :
    sampleEval z (genericComplexGramResultant m n) =
      resultant (complexGram (complexSampleMatrix z)).charpoly
        (complexGram (complexSampleMatrix z)).charpoly.derivative := by
  have hcp : (complexGram (complexSampleMatrix z)).charpoly =
      (genericComplexGram m n).charpoly.map (sampleEval z) := by
    rw [← charpoly_map, genericComplexGram_map]
  have hdv : (complexGram (complexSampleMatrix z)).charpoly.derivative =
      ((genericComplexGram m n).charpoly.derivative).map (sampleEval z) := by
    rw [hcp, derivative_map]
  have hnd1 : (complexGram (complexSampleMatrix z)).charpoly.natDegree = n := by
    simp
  have hnd2 : (complexGram (complexSampleMatrix z)).charpoly.derivative.natDegree = n - 1 := by
    rw [Polynomial.natDegree_derivative, hnd1]
  have hkey :
      resultant (complexGram (complexSampleMatrix z)).charpoly
          (complexGram (complexSampleMatrix z)).charpoly.derivative n (n - 1) =
        resultant (complexGram (complexSampleMatrix z)).charpoly
          (complexGram (complexSampleMatrix z)).charpoly.derivative := by
    rw [hnd1, hnd2]
  unfold genericComplexGramResultant
  rw [← hkey, hdv, hcp, resultant_map_map]

/-! ### Nonzero resultant forces simple Hermitian spectrum -/

/-- If the charpoly/derivative resultant of a Hermitian matrix is nonzero, its
ordered eigenvalues are pairwise distinct. -/
theorem hermitian_eigenvalues₀_injective_of_resultant_ne_zero {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (h : resultant A.charpoly A.charpoly.derivative ≠ 0) :
    Function.Injective hA.eigenvalues₀ := by
  have hcop : IsCoprime A.charpoly A.charpoly.derivative := by
    by_contra hnc
    exact h (resultant_eq_zero_iff.mpr ⟨Or.inl (Matrix.charpoly_monic A).ne_zero, hnc⟩)
  have hsep : A.charpoly.Separable := hcop
  rw [hA.charpoly_eq, Polynomial.separable_prod_X_sub_C_iff] at hsep
  have hinj : Function.Injective hA.eigenvalues := fun i j hij =>
    hsep (by simp only [hij])
  let e : Fin (Fintype.card (Fin d)) ≃ Fin d := Fintype.equivOfCardEq (Fintype.card_fin _)
  intro i j hij
  apply e.injective
  apply hinj
  simp only [Matrix.IsHermitian.eigenvalues]
  simpa [e] using hij

/-! ### A diagonal witness: the generic resultant is nonzero when `n ≤ m` -/

/-- Mean matrix with `√`-free real diagonal `1, 2, …, n` embedded in the first
`n` rows. -/
def witnessMean (hnm : n ≤ m) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => if i = Fin.castLE hnm j then ((((j : ℕ) : ℝ) + 1 : ℝ) : ℂ) else 0

theorem complexGram_witnessMean (hnm : n ≤ m) :
    complexGram (witnessMean hnm) =
      diagonal (fun j : Fin n => (((((j : ℕ) : ℝ) + 1) ^ 2 : ℝ) : ℂ)) := by
  ext j k
  simp only [complexGram, Matrix.mul_apply, Matrix.conjTranspose_apply, witnessMean,
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

theorem complexSampleMatrix_zero :
    complexSampleMatrix (0 : ComplexSample (m := m) (n := n)) = 0 := by
  ext i j
  simp [complexSampleMatrix]

theorem complexSampleMatrix_complexSampleMean (M : Matrix (Fin m) (Fin n) ℂ) :
    complexSampleMatrix (complexSampleMean M) = M := by
  have h := complexSampleMatrix_add_mean (0 : ComplexSample (m := m) (n := n)) M
  rw [zero_add, complexSampleMatrix_zero, zero_add] at h
  exact h

/-- The generic complex Gram resultant is a nonzero polynomial when `n ≤ m`. -/
theorem genericComplexGramResultant_ne_zero (hnm : n ≤ m) :
    genericComplexGramResultant m n ≠ 0 := by
  intro hzero
  have key := genericComplexGramResultant_eval (complexSampleMean (witnessMean hnm))
  rw [hzero, map_zero, complexSampleMatrix_complexSampleMean,
    complexGram_witnessMean] at key
  have hsep : (diagonal (fun j : Fin n =>
      (((((j : ℕ) : ℝ) + 1) ^ 2 : ℝ) : ℂ))).charpoly.Separable := by
    rw [Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
    intro i j h
    have hR : (((i : ℕ) : ℝ) + 1) ^ 2 = (((j : ℕ) : ℝ) + 1) ^ 2 :=
      Complex.ofReal_injective h
    have hR' : ((i : ℕ) : ℝ) + 1 = ((j : ℕ) : ℝ) + 1 :=
      (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp hR
    have hN : (i : ℕ) = (j : ℕ) := by exact_mod_cast (add_right_cancel hR')
    exact Fin.ext hN
  exact resultant_ne_zero _ _ hsep key.symm

/-! ### Probability one -/

theorem complexSample_genericResultant_zeroSet_volume (hnm : n ≤ m) :
    volume {z : ComplexSample (m := m) (n := n) |
      sampleEval z (genericComplexGramResultant m n) = 0} = 0 := by
  have hfun := complexMvPolynomial_realZeroSet_volume_eq_zero _
    (genericComplexGramResultant_ne_zero (m := m) (n := n) hnm)
  let e : (SampleIdx m n → ℝ) ≃ᵐ ComplexSample (m := m) (n := n) :=
    MeasurableEquiv.toLp 2 _
  have hpres : MeasurePreserving e volume volume :=
    PiLp.volume_preserving_toLp (SampleIdx m n)
  have hpre : e ⁻¹' {z : ComplexSample (m := m) (n := n) |
      sampleEval z (genericComplexGramResultant m n) = 0} =
      {x : SampleIdx m n → ℝ |
        MvPolynomial.eval (fun i => (x i : ℂ)) (genericComplexGramResultant m n) = 0} := by
    ext x
    simp [e, sampleEval]
  rw [← hpres.measure_preimage_equiv, hpre]
  exact hfun

/-- **Simple spectrum, any dimension.** For `n ≤ m` and every deterministic
complex mean `M`, the ordered eigenvalues of the actual shifted complex Gaussian
Gram matrix `(X + M)ᴴ (X + M)` are pairwise distinct almost surely. -/
theorem complexSample_shiftedGram_eigenvalues_injective_ae (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      Function.Injective
        (complexGram_posSemidef (complexSampleMatrix z + M)).1.eigenvalues₀ := by
  let S := {z : ComplexSample (m := m) (n := n) |
    sampleEval z (genericComplexGramResultant m n) = 0}
  have hS : volume S = 0 := complexSample_genericResultant_zeroSet_volume hnm
  have hshift : volume ((fun z => z + complexSampleMean M) ⁻¹' S) = 0 := by
    rw [measure_preimage_add_right]
    exact hS
  have hac : stdGaussian (ComplexSample (m := m) (n := n))
      ((fun z => z + complexSampleMean M) ⁻¹' S) = 0 := by
    rw [stdGaussian_euclidean_eq_radialDensity]
    exact withDensity_absolutelyContinuous volume _ hshift
  rw [ae_iff]
  apply measure_mono_null _ hac
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  simp only [Set.mem_preimage, S, Set.mem_ofPred_eq]
  by_contra hne
  apply hz
  apply hermitian_eigenvalues₀_injective_of_resultant_ne_zero
  rw [← complexSampleMatrix_add_mean, ← genericComplexGramResultant_eval]
  exact hne

/-- Equivalently, the ordered eigenvalues are strictly decreasing almost surely. -/
theorem complexSample_shiftedGram_eigenvalues_strictAnti_ae (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      StrictAnti
        (complexGram_posSemidef (complexSampleMatrix z + M)).1.eigenvalues₀ := by
  filter_upwards [complexSample_shiftedGram_eigenvalues_injective_ae hnm M] with z hz
  exact (Matrix.IsHermitian.eigenvalues₀_antitone _).strictAnti_of_injective hz

/-! ### Row Gram `X Xᴴ` (for `m ≤ n`) and the paper's smaller-side Gram -/

/-- The generic row Gram matrix `X Xᴴ`. -/
def genericComplexRowGram (m n : ℕ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (SampleIdx m n) ℂ) :=
  genericComplexSample m n * genericComplexSampleConjT m n

def genericComplexRowGramResultant (m n : ℕ) : MvPolynomial (SampleIdx m n) ℂ :=
  resultant (genericComplexRowGram m n).charpoly
    (genericComplexRowGram m n).charpoly.derivative m (m - 1)

theorem genericComplexRowGram_map (z : ComplexSample (m := m) (n := n)) :
    (genericComplexRowGram m n).map (sampleEval z) =
      complexSampleMatrix z * (complexSampleMatrix z)ᴴ := by
  rw [genericComplexRowGram, Matrix.map_mul, genericComplexSampleConjT_map,
    genericComplexSample_map]

theorem genericComplexRowGramResultant_eval (z : ComplexSample (m := m) (n := n)) :
    sampleEval z (genericComplexRowGramResultant m n) =
      resultant (complexSampleMatrix z * (complexSampleMatrix z)ᴴ).charpoly
        (complexSampleMatrix z * (complexSampleMatrix z)ᴴ).charpoly.derivative := by
  set A := complexSampleMatrix z * (complexSampleMatrix z)ᴴ
  have hcp : A.charpoly = (genericComplexRowGram m n).charpoly.map (sampleEval z) := by
    rw [← charpoly_map, genericComplexRowGram_map]
  have hdv : A.charpoly.derivative =
      ((genericComplexRowGram m n).charpoly.derivative).map (sampleEval z) := by
    rw [hcp, derivative_map]
  have hnd1 : A.charpoly.natDegree = m := by simp
  have hnd2 : A.charpoly.derivative.natDegree = m - 1 := by
    rw [Polynomial.natDegree_derivative, hnd1]
  have hkey : resultant A.charpoly A.charpoly.derivative m (m - 1) =
      resultant A.charpoly A.charpoly.derivative := by
    rw [hnd1, hnd2]
  unfold genericComplexRowGramResultant
  rw [← hkey, hdv, hcp, resultant_map_map]

/-- Row witness mean: real diagonal `1, 2, …, m` in the first `m` columns. -/
def witnessRowMean (hmn : m ≤ n) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => if j = Fin.castLE hmn i then ((((i : ℕ) : ℝ) + 1 : ℝ) : ℂ) else 0

theorem rowGram_witnessRowMean (hmn : m ≤ n) :
    witnessRowMean hmn * (witnessRowMean hmn)ᴴ =
      diagonal (fun i : Fin m => (((((i : ℕ) : ℝ) + 1) ^ 2 : ℝ) : ℂ)) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, witnessRowMean,
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

/-- Separability of a diagonal with entries `(k+1)²`. -/
private theorem diag_sq_separable (d : ℕ) :
    (diagonal (fun k : Fin d => (((((k : ℕ) : ℝ) + 1) ^ 2 : ℝ) : ℂ))).charpoly.Separable := by
  rw [Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
  intro i j h
  have hR : (((i : ℕ) : ℝ) + 1) ^ 2 = (((j : ℕ) : ℝ) + 1) ^ 2 :=
    Complex.ofReal_injective h
  have hR' : ((i : ℕ) : ℝ) + 1 = ((j : ℕ) : ℝ) + 1 :=
    (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp hR
  have hN : (i : ℕ) = (j : ℕ) := by exact_mod_cast (add_right_cancel hR')
  exact Fin.ext hN

theorem genericComplexRowGramResultant_ne_zero (hmn : m ≤ n) :
    genericComplexRowGramResultant m n ≠ 0 := by
  intro hzero
  have key := genericComplexRowGramResultant_eval (complexSampleMean (witnessRowMean hmn))
  rw [hzero, map_zero, complexSampleMatrix_complexSampleMean,
    rowGram_witnessRowMean] at key
  exact resultant_ne_zero _ _ (diag_sq_separable m) key.symm

/-- A generic nonzero sample polynomial avoids the shifted Gaussian sample a.s. -/
theorem sampleEval_ne_zero_ae {P : MvPolynomial (SampleIdx m n) ℂ} (hP : P ≠ 0)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      sampleEval (z + complexSampleMean M) P ≠ 0 := by
  let S := {z : ComplexSample (m := m) (n := n) | sampleEval z P = 0}
  have hS : volume S = 0 := by
    have hfun := complexMvPolynomial_realZeroSet_volume_eq_zero _ hP
    let e : (SampleIdx m n → ℝ) ≃ᵐ ComplexSample (m := m) (n := n) :=
      MeasurableEquiv.toLp 2 _
    have hpres : MeasurePreserving e volume volume :=
      PiLp.volume_preserving_toLp (SampleIdx m n)
    have hpre : e ⁻¹' S =
        {x : SampleIdx m n → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) P = 0} := by
      ext x
      simp [e, S, sampleEval]
    rw [← hpres.measure_preimage_equiv, hpre]
    exact hfun
  have hshift : volume ((fun z => z + complexSampleMean M) ⁻¹' S) = 0 := by
    rw [measure_preimage_add_right]
    exact hS
  have hac : stdGaussian (ComplexSample (m := m) (n := n))
      ((fun z => z + complexSampleMean M) ⁻¹' S) = 0 := by
    rw [stdGaussian_euclidean_eq_radialDensity]
    exact withDensity_absolutelyContinuous volume _ hshift
  rw [ae_iff]
  apply measure_mono_null _ hac
  intro z hz
  simpa [S] using hz

/-- **Paper-facing simple spectrum.** For every rectangular shape `m × n` and
every deterministic complex mean `M`, the ordered eigenvalues of the paper's
smaller-side (`s = min m n`) Gram matrix of the shifted complex Gaussian sample
are pairwise distinct almost surely. -/
theorem paperSmallSideGram_eigenvalues_injective_ae
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      Function.Injective
        (paperSmallSideGram_posSemidef (complexSampleMatrix z + M)).1.eigenvalues₀ := by
  classical
  by_cases hmn : m ≤ n
  · filter_upwards [sampleEval_ne_zero_ae (genericComplexRowGramResultant_ne_zero hmn) M]
      with z hz
    apply hermitian_eigenvalues₀_injective_of_resultant_ne_zero
    rw [genericComplexRowGramResultant_eval, complexSampleMatrix_add_mean] at hz
    have hcp : (paperSmallSideGram (complexSampleMatrix z + M)).charpoly =
        ((complexSampleMatrix z + M) * (complexSampleMatrix z + M)ᴴ).charpoly := by
      unfold paperSmallSideGram
      rw [dif_pos hmn]
      exact charpoly_submatrix_equiv _ _
    rw [hcp]
    exact hz
  · have hnm : n ≤ m := le_of_not_ge hmn
    filter_upwards [sampleEval_ne_zero_ae (genericComplexGramResultant_ne_zero hnm) M]
      with z hz
    apply hermitian_eigenvalues₀_injective_of_resultant_ne_zero
    rw [genericComplexGramResultant_eval, complexSampleMatrix_add_mean] at hz
    have hcp : (paperSmallSideGram (complexSampleMatrix z + M)).charpoly =
        (complexGram (complexSampleMatrix z + M)).charpoly := by
      unfold paperSmallSideGram
      rw [dif_neg hmn]
      exact charpoly_submatrix_equiv _ _
    rw [hcp]
    exact hz

/-- The paper's ordered spectrum `φ₁ > φ₂ > ⋯ > φ_s` is strict almost surely. -/
theorem paperSmallSideGram_eigenvalues_strictAnti_ae
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      StrictAnti
        (paperSmallSideGram_posSemidef (complexSampleMatrix z + M)).1.eigenvalues₀ := by
  filter_upwards [paperSmallSideGram_eigenvalues_injective_ae M] with z hz
  exact (Matrix.IsHermitian.eigenvalues₀_antitone _).strictAnti_of_injective hz

end

end JinWishart
