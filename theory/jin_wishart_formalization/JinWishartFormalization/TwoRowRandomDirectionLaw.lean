import JinWishartFormalization.ComplexTwoRowResidualEnergy
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Actual two-column Gaussian law in its random first-column direction

The direction is explicitly measurable and unit even at a zero first column.
Use the existing skew-product theorem, not an assumption that the random
direction is independent of the first column.
[需人工审查] Random direction, zero fallback and actual complex variance conventions.
-/

open MeasureTheory ProbabilityTheory

namespace JinWishart
noncomputable section

def twoRowUnitDirection (x : ComplexColumnSpace 2) : ComplexColumnSpace 2 :=
  if x = 0 then EuclideanSpace.single (0 : Fin 2) (1 : ℂ) else NormedSpace.normalize x

theorem twoRowUnitDirection_norm (x : ComplexColumnSpace 2) :
    ‖twoRowUnitDirection x‖ = 1 := by
  by_cases hx : x = 0
  · simp [twoRowUnitDirection, hx]
  · simp only [twoRowUnitDirection, ite_eq_right hx]
    exact NormedSpace.norm_normalize hx

theorem measurable_twoRowUnitDirection : Measurable twoRowUnitDirection := by
  unfold twoRowUnitDirection NormedSpace.normalize
  apply Measurable.ite (measurableSet_singleton (0 : ComplexColumnSpace 2))
  · fun_prop
  · fun_prop

theorem twoRowUnitDirection_reconstruct (x : ComplexColumnSpace 2) :
    ‖x‖ • twoRowUnitDirection x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [twoRowUnitDirection, ite_eq_right hx, NormedSpace.norm_smul_normalize]

def twoRowFiberCoordinates (u v : TwoColumnBlock 2) : ℂ × ℝ :=
  (inner ℂ (twoRowUnitDirection (actualComplexColumn u)) (actualComplexColumn v),
    ‖complexOrthogonalResidual (twoRowUnitDirection (actualComplexColumn u))
      (actualComplexColumn v)‖ ^ 2)

theorem measurable_twoRowFiberCoordinates :
    Measurable (Function.uncurry twoRowFiberCoordinates) := by
  have hm : Measurable (actualComplexColumn (m := 2)) := by
    unfold actualComplexColumn
    fun_prop
  have ha : Measurable (fun p : TwoColumnBlock 2 × TwoColumnBlock 2 =>
      twoRowUnitDirection (actualComplexColumn p.1)) :=
    measurable_twoRowUnitDirection.comp (hm.comp measurable_fst)
  have hb : Measurable (fun p : TwoColumnBlock 2 × TwoColumnBlock 2 =>
      actualComplexColumn p.2) := hm.comp measurable_snd
  unfold twoRowFiberCoordinates Function.uncurry
  simp only [complexOrthogonalResidual_apply]
  fun_prop

/-- Exact fixed-fiber law, now for every first-column value including zero. -/
theorem twoRowFiberCoordinates_law (u : TwoColumnBlock 2) :
    (stdGaussian (TwoColumnBlock 2)).map (twoRowFiberCoordinates u) =
      ((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1) :=
  actualTwoRow_projection_residualEnergy_joint_law _ (twoRowUnitDirection_norm _)

/-- First column, normalized complex projection and residual energy have a product law. -/
theorem twoRowRandomDirection_product_law :
    MeasurePreserving
      (fun p : TwoColumnBlock 2 × TwoColumnBlock 2 =>
        (p.1, twoRowFiberCoordinates p.1 p.2))
      ((stdGaussian (TwoColumnBlock 2)).prod (stdGaussian (TwoColumnBlock 2)))
      ((stdGaussian (TwoColumnBlock 2)).prod
        (((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1))) := by
  exact (MeasurePreserving.id (stdGaussian (TwoColumnBlock 2))).skew_product
    measurable_twoRowFiberCoordinates (Filter.Eventually.of_forall twoRowFiberCoordinates_law)

/-- Same joint law on the actual 2-by-2 sample space, not merely a defined product model. -/
theorem actualTwoRow_randomDirection_joint_law :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
      (fun z => ((twoColumnSplit z).1,
        twoRowFiberCoordinates (twoColumnSplit z).1 (twoColumnSplit z).2)) =
      (stdGaussian (TwoColumnBlock 2)).prod
        (((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1)) := by
  change (stdGaussian (ComplexSample (m := 2) (n := 2))).map
    ((fun p : TwoColumnBlock 2 × TwoColumnBlock 2 =>
      (p.1, twoRowFiberCoordinates p.1 p.2)) ∘ twoColumnSplit) = _
  rw [← Measure.map_map twoRowRandomDirection_product_law.measurable
    measurable_twoColumnSplit, twoColumnSplit_law,
    twoRowRandomDirection_product_law.map_eq]

theorem twoRowFiberCoordinates_offDiagonal (u v : TwoColumnBlock 2) :
    inner ℂ (actualComplexColumn u) (actualComplexColumn v) =
      (‖actualComplexColumn u‖ : ℂ) * (twoRowFiberCoordinates u v).1 := by
  have h := congrArg (fun x : ComplexColumnSpace 2 => inner ℂ x (actualComplexColumn v))
    (twoRowUnitDirection_reconstruct (actualComplexColumn u))
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left] at h
  simpa [twoRowFiberCoordinates] using h.symm

theorem twoRowFiberCoordinates_secondEnergy (u v : TwoColumnBlock 2) :
    ‖actualComplexColumn v‖ ^ 2 =
      ‖(twoRowFiberCoordinates u v).1‖ ^ 2 + (twoRowFiberCoordinates u v).2 :=
  complexOrthogonalResidual_norm_sq _ _ (twoRowUnitDirection_norm _)

/-- Deterministic Hermitian Gram reconstruction from actual first column and two fiber coordinates. -/
def twoRowGramFromCoordinates (p : TwoColumnBlock 2 × (ℂ × ℝ)) :
    Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 0 then
    if j = 0 then (‖actualComplexColumn p.1‖ ^ 2 : ℝ)
    else (‖actualComplexColumn p.1‖ : ℂ) * p.2.1
  else
    if j = 0 then star ((‖actualComplexColumn p.1‖ : ℂ) * p.2.1)
    else (‖p.2.1‖ ^ 2 + p.2.2 : ℝ)

theorem measurable_twoRowGramFromCoordinates : Measurable twoRowGramFromCoordinates := by
  unfold twoRowGramFromCoordinates actualComplexColumn
  fun_prop

theorem twoRow_actualGram_reconstruction (u v : TwoColumnBlock 2) :
    complexGram (complexSampleMatrix (twoColumnJoin (u, v))) =
      twoRowGramFromCoordinates (u, twoRowFiberCoordinates u v) := by
  rw [twoColumnJoin_matrix_eq_columnPair]
  ext i j
  rw [complexColumnPair_gram_entry]
  fin_cases i <;> fin_cases j
  · simp [twoRowGramFromCoordinates, inner_self_eq_norm_sq_to_K]
  · simpa [twoRowGramFromCoordinates] using twoRowFiberCoordinates_offDiagonal u v
  · simpa [twoRowGramFromCoordinates, inner_conj_symm] using
      congrArg star (twoRowFiberCoordinates_offDiagonal u v)
  · simpa [twoRowGramFromCoordinates, inner_self_eq_norm_sq_to_K] using
      congrArg (fun r : ℝ => (r : ℂ)) (twoRowFiberCoordinates_secondEnergy u v)

/-- Actual central 2-by-2 Gram law is an explicit pushforward of independent coordinates.
This is not yet a Lebesgue Gram density or an ordered spectral density. -/
theorem actualTwoRow_GramLaw_eq_coordinate_pushforward :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
      (fun z => complexGram (complexSampleMatrix z)) =
      ((stdGaussian (TwoColumnBlock 2)).prod
        (((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1))).map
        twoRowGramFromCoordinates := by
  have hm : Measurable (fun z : ComplexSample (m := 2) (n := 2) =>
      ((twoColumnSplit z).1,
        twoRowFiberCoordinates (twoColumnSplit z).1 (twoColumnSplit z).2)) :=
    twoRowRandomDirection_product_law.measurable.comp measurable_twoColumnSplit
  rw [← actualTwoRow_randomDirection_joint_law,
    Measure.map_map measurable_twoRowGramFromCoordinates hm]
  congr 1
  funext z
  simpa only [Function.comp_apply, Prod.mk.eta, twoColumnJoin_split] using
    twoRow_actualGram_reconstruction (twoColumnSplit z).1 (twoColumnSplit z).2

theorem actualTwoRow_columnEnergy_eq (v : TwoColumnBlock 2) :
    ‖actualComplexColumn v‖ ^ 2 = euclideanGaussianEnergy v := by
  unfold actualComplexColumn
  rw [norm_smul, (complexColumnCoordinates 2).norm_map]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt 2)⁻¹)]
  unfold euclideanGaussianEnergy
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  nlinarith

/-- Reuse the established radial law; do not redo a one-column density proof. -/
theorem actualTwoRow_columnEnergy_law :
    (stdGaussian (TwoColumnBlock 2)).map (fun v => ‖actualComplexColumn v‖ ^ 2) =
      gammaMeasure 2 1 := by
  simp_rw [actualTwoRow_columnEnergy_eq]
  apply stdGaussian_euclideanEnergy_map_eq_gammaMeasure 2
  · simp
  · norm_num

def twoRowBartlettCoordinates (z : ComplexSample (m := 2) (n := 2)) : ℝ × (ℂ × ℝ) :=
  (‖actualComplexColumn (twoColumnSplit z).1‖ ^ 2,
    twoRowFiberCoordinates (twoColumnSplit z).1 (twoColumnSplit z).2)

/-- Actual minimal complex Bartlett coordinates are independent Gamma(2,1), CN(0,1), Exp(1). -/
theorem actualTwoRow_BartlettCoordinates_law :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map twoRowBartlettCoordinates =
      (gammaMeasure 2 1).prod
        (((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1)) := by
  have hm : Measurable (fun v : TwoColumnBlock 2 => ‖actualComplexColumn v‖ ^ 2) := by
    unfold actualComplexColumn
    fun_prop
  have hp := (show MeasurePreserving (fun v : TwoColumnBlock 2 => ‖actualComplexColumn v‖ ^ 2)
      (stdGaussian (TwoColumnBlock 2)) (gammaMeasure 2 1) from
      ⟨hm, actualTwoRow_columnEnergy_law⟩).skew_product
        measurable_twoRowFiberCoordinates
        (Filter.Eventually.of_forall twoRowFiberCoordinates_law)
  change (stdGaussian (ComplexSample (m := 2) (n := 2))).map
    ((fun p : TwoColumnBlock 2 × TwoColumnBlock 2 =>
      (‖actualComplexColumn p.1‖ ^ 2, twoRowFiberCoordinates p.1 p.2)) ∘ twoColumnSplit) = _
  rw [← Measure.map_map hp.measurable measurable_twoColumnSplit, twoColumnSplit_law, hp.map_eq]

theorem measurable_twoRowBartlettCoordinates : Measurable twoRowBartlettCoordinates := by
  have hf : Measurable (fun z : ComplexSample (m := 2) (n := 2) =>
      twoRowFiberCoordinates (twoColumnSplit z).1 (twoColumnSplit z).2) :=
    measurable_twoRowFiberCoordinates.comp measurable_twoColumnSplit
  have he : Measurable (fun z : ComplexSample (m := 2) (n := 2) =>
      ‖actualComplexColumn (twoColumnSplit z).1‖ ^ 2) := by
    unfold actualComplexColumn
    fun_prop
  exact he.prodMk hf

/-- Four real coordinates of a Hermitian Gram matrix, with angle variables removed. -/
def twoRowBartlettGram (p : ℝ × (ℂ × ℝ)) : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 0 then
    if j = 0 then p.1 else (Real.sqrt p.1 : ℂ) * p.2.1
  else
    if j = 0 then star ((Real.sqrt p.1 : ℂ) * p.2.1)
    else (‖p.2.1‖ ^ 2 + p.2.2 : ℝ)

theorem measurable_twoRowBartlettGram : Measurable twoRowBartlettGram := by
  unfold twoRowBartlettGram
  fun_prop

theorem twoRowGramFromCoordinates_eq_BartlettGram
    (u : TwoColumnBlock 2) (q : ℂ × ℝ) :
    twoRowGramFromCoordinates (u, q) =
      twoRowBartlettGram (‖actualComplexColumn u‖ ^ 2, q) := by
  ext i j
  simp only [twoRowGramFromCoordinates, twoRowBartlettGram,
    Real.sqrt_sq (norm_nonneg (actualComplexColumn u))]

/-- Actual central Gram law on independent four-real-dimensional Bartlett coordinates.
The next missing step is a justified Jacobian, not Gaussian angle independence. -/
theorem actualTwoRow_GramLaw_eq_Bartlett_pushforward :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
      (fun z => complexGram (complexSampleMatrix z)) =
      ((gammaMeasure 2 1).prod
        (((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1))).map
        twoRowBartlettGram := by
  rw [← actualTwoRow_BartlettCoordinates_law,
    Measure.map_map measurable_twoRowBartlettGram measurable_twoRowBartlettCoordinates]
  congr 1
  funext z
  change complexGram (complexSampleMatrix z) = twoRowBartlettGram
    (‖actualComplexColumn (twoColumnSplit z).1‖ ^ 2,
      twoRowFiberCoordinates (twoColumnSplit z).1 (twoColumnSplit z).2)
  rw [← twoRowGramFromCoordinates_eq_BartlettGram]
  simpa only [Prod.mk.eta, twoColumnJoin_split] using
    twoRow_actualGram_reconstruction (twoColumnSplit z).1 (twoColumnSplit z).2

end
end JinWishart
