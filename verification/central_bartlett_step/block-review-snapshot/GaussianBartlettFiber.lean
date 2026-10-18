import JinWishartFormalization.GaussianMatrixBlockLaw

/-!
# The full fixed-column Gaussian Bartlett fiber, not just residual trace

Codex proofs. For each fixed nonzero u, use one existential complex unitary
inside the proof. The observable itself is the explicit measurable normalized
inner-product vector and residual Gram. A measurable family of frames is
neither assumed nor constructed. [需人工审查] Joint measurability, complex
inner-product convention and the future skew-product application.
-/

open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def normalizedColumnCoefficients {m n : ℕ} (u : EuclideanSpace ℂ (Fin (m + 1)))
    (V : Matrix (Fin (m + 1)) (Fin n) ℂ) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun j => inner ℂ u (complexMatrixColumn V j) / (‖u‖ : ℂ))

def complexVectorGramRankOne {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ := fun j k => star (z j) * z k

def projectedResidualGram {m n : ℕ} (u : EuclideanSpace ℂ (Fin (m + 1)))
    (V : Matrix (Fin (m + 1)) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  complexGram V - complexVectorGramRankOne (normalizedColumnCoefficients u V)

theorem measurable_complexGram_map (m n : ℕ) :
    Measurable (complexGram (m := m) (n := n)) := by
  exact (show Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => Aᴴ * A) by fun_prop).measurable

theorem measurable_normalizedColumnCoefficients (m n : ℕ) :
    Measurable (fun p : EuclideanSpace ℂ (Fin (m + 1)) ×
      Matrix (Fin (m + 1)) (Fin n) ℂ => normalizedColumnCoefficients p.1 p.2) := by
  unfold normalizedColumnCoefficients complexMatrixColumn
  fun_prop

theorem measurable_projectedResidualGram (m n : ℕ) :
    Measurable (fun p : EuclideanSpace ℂ (Fin (m + 1)) ×
      Matrix (Fin (m + 1)) (Fin n) ℂ => projectedResidualGram p.1 p.2) := by
  have hG := (measurable_complexGram_map (m + 1) n).comp
    (measurable_snd : Measurable
      (Prod.snd : EuclideanSpace ℂ (Fin (m + 1)) ×
        Matrix (Fin (m + 1)) (Fin n) ℂ → Matrix (Fin (m + 1)) (Fin n) ℂ))
  have hz := (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℂ)).measurable.comp
    (measurable_normalizedColumnCoefficients m n)
  apply Measurable.of_eval_matrix
  intro j k
  exact hG.eval_matrix.sub ((Complex.continuous_conj.measurable.comp hz.eval).mul hz.eval)

theorem complexGram_firstRow_split {m n : ℕ} (V : Matrix (Fin (m + 1)) (Fin n) ℂ) :
    complexGram V = complexVectorGramRankOne (matrixFirstRow V) +
      complexGram (matrixRemainingRows V) := by
  ext j k
  simp only [complexGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.add_apply, complexVectorGramRankOne, matrixFirstRow, matrixRemainingRows,
    Fin.sum_univ_succ]

theorem normalizedColumnCoefficients_frame {m n : ℕ}
    (u : EuclideanSpace ℂ (Fin (m + 1))) (hu : u ≠ 0)
    (U : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (hU : U u = ‖u‖ • complexFirstBasisVector m)
    (V : Matrix (Fin (m + 1)) (Fin n) ℂ) :
    normalizedColumnCoefficients u V = matrixFirstRow (unitaryActColumns U V) := by
  ext j
  change inner ℂ u (complexMatrixColumn V j) / (‖u‖ : ℂ) =
    U (complexMatrixColumn V j) 0
  have h := U.inner_map_map u (complexMatrixColumn V j)
  rw [hU] at h
  have hc : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hu
  have hinner : (‖u‖ : ℂ) * U (complexMatrixColumn V j) 0 =
      inner ℂ u (complexMatrixColumn V j) := by
    simpa [complexFirstBasisVector, inner_smul_left_eq_smul,
      EuclideanSpace.inner_single_left, Complex.real_smul] using h
  symm
  exact (eq_div_iff hc).2 (by simpa only [mul_comm] using hinner)

theorem projectedResidualGram_frame {m n : ℕ}
    (u : EuclideanSpace ℂ (Fin (m + 1))) (hu : u ≠ 0)
    (U : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (hU : U u = ‖u‖ • complexFirstBasisVector m)
    (V : Matrix (Fin (m + 1)) (Fin n) ℂ) :
    projectedResidualGram u V = complexGram (matrixRemainingRows (unitaryActColumns U V)) := by
  rw [projectedResidualGram, normalizedColumnCoefficients_frame u hu U hU,
    ← complexGram_unitaryActColumns U V, complexGram_firstRow_split]
  exact add_sub_cancel_left _ _

theorem complexGaussianMatrixLaw_map_gram (m n : ℕ) :
    (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ)).map complexGram =
      complexWishart (m := m) (n := n) := by
  unfold complexGaussianMatrixLaw complexWishart
  rw [Measure.map_map (measurable_complexGram_map m n)
    (measurable_shiftedComplexSampleMatrix _)]
  congr 1
  funext z
  simp only [Function.comp_def, add_zero, complexSampleGram]

def centralBartlettFiber {m n : ℕ} (u : EuclideanSpace ℂ (Fin (m + 1)))
    (V : Matrix (Fin (m + 1)) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℂ :=
  (normalizedColumnCoefficients u V, projectedResidualGram u V)

theorem measurable_centralBartlettFiber (m n : ℕ) :
    Measurable (Function.uncurry (centralBartlettFiber (m := m) (n := n))) :=
  (measurable_normalizedColumnCoefficients m n).prodMk
    (measurable_projectedResidualGram m n)

/-- Full actual joint law of normalized coefficients and residual Gram for fixed u. -/
theorem centralBartlettFiber_law {m n : ℕ} (u : EuclideanSpace ℂ (Fin (m + 1)))
    (hu : u ≠ 0) :
    (complexGaussianMatrixLaw (0 : Matrix (Fin (m + 1)) (Fin n) ℂ)).map
      (centralBartlettFiber u) =
      (standardComplexColumnLaw n).prod (complexWishart (m := m) (n := n)) := by
  obtain ⟨U, hU⟩ := exists_complex_nonzero_frame m u hu
  have hfun : centralBartlettFiber (n := n) u =
      Prod.map id complexGram ∘ matrixRowSplit ∘ unitaryActColumns U := by
    funext V
    exact Prod.ext (normalizedColumnCoefficients_frame u hu U hU V)
      (projectedResidualGram_frame u hu U hU V)
  rw [hfun, ← Measure.map_map (measurable_id.prodMap (measurable_complexGram_map m n))
    ((measurable_matrixRowSplit m n).comp (measurable_unitaryActColumns U)),
    ← Measure.map_map (measurable_matrixRowSplit m n) (measurable_unitaryActColumns U),
    complexGaussianMatrixLaw_unitary_invariant, complexGaussianMatrixLaw_rowSplit,
    ← Measure.map_prod_map _ _ measurable_id (measurable_complexGram_map m n),
    Measure.map_id, complexGaussianMatrixLaw_map_gram]

end
end JinWishart

#print axioms JinWishart.measurable_normalizedColumnCoefficients
#print axioms JinWishart.measurable_projectedResidualGram
#print axioms JinWishart.complexGram_firstRow_split
#print axioms JinWishart.normalizedColumnCoefficients_frame
#print axioms JinWishart.projectedResidualGram_frame
#print axioms JinWishart.measurable_complexGram_map
#print axioms JinWishart.complexGaussianMatrixLaw_map_gram
#print axioms JinWishart.measurable_centralBartlettFiber
#print axioms JinWishart.centralBartlettFiber_law
