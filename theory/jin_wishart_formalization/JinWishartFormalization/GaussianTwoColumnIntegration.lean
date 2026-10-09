import JinWishartFormalization.GaussianMatrixSpectralIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Splitting actual two-column Gaussian integration

Fixed-coordinate Gaussian product structure is made explicit before any
first-column-dependent rotation. This does not assert conditional QR/Bartlett
or Gram/spectral density. [需人工审查] Fubini and actual column interpretation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace JinWishart

noncomputable section

def euclideanGaussianSplit {ι κ : Type*} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ (ι ⊕ κ)) : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ :=
  (WithLp.toLp 2 (fun i => z (.inl i)), WithLp.toLp 2 (fun j => z (.inr j)))

theorem measurable_euclideanGaussianSplit {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Measurable (euclideanGaussianSplit (ι := ι) (κ := κ)) := by
  unfold euclideanGaussianSplit
  fun_prop

/-- Gaussian blocks with disjoint coordinates have the actual product law. -/
theorem stdGaussian_sum_split {ι κ : Type*} [Fintype ι] [Fintype κ] :
    (stdGaussian (EuclideanSpace ℝ (ι ⊕ κ))).map euclideanGaussianSplit =
      (stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ κ)) := by
  rw [← map_pi_eq_stdGaussian,
    Measure.map_map measurable_euclideanGaussianSplit (by fun_prop)]
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)
  have hsplit := (measurePreserving_sumPiEquivProdPi
    (fun _ : ι ⊕ κ => gaussianReal 0 1)).map_eq
  have hfun : (euclideanGaussianSplit ∘ WithLp.toLp 2) =
      Prod.map (WithLp.toLp 2) (WithLp.toLp 2) ∘ e := rfl
  rw [hfun, ← Measure.map_map (by fun_prop) e.measurable, hsplit,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    map_pi_eq_stdGaussian, map_pi_eq_stdGaussian]

/-- A concrete reindexing identifies the first and second column coordinates. -/
def twoColumnIndexEquiv (m : ℕ) :
    ((Fin m × Fin 2) ⊕ (Fin m × Fin 2)) ≃ ((Fin m × Fin 2) × Fin 2) where
  toFun := fun x => Sum.elim (fun ik => ((ik.1, 0), ik.2))
    (fun ik => ((ik.1, 1), ik.2)) x
  invFun := fun ijk => if ijk.1.2 = 0 then .inl (ijk.1.1, ijk.2)
    else .inr (ijk.1.1, ijk.2)
  left_inv := by intro x; cases x <;> simp
  right_inv := by
    rintro ⟨⟨i, j⟩, k⟩
    fin_cases j <;> simp

abbrev TwoColumnBlock (m : ℕ) := EuclideanSpace ℝ (Fin m × Fin 2)

def twoColumnReindex (m : ℕ) : ComplexSample (m := m) (n := 2) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ ((Fin m × Fin 2) ⊕ (Fin m × Fin 2)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (twoColumnIndexEquiv m).symm

def twoColumnSplit {m : ℕ} (z : ComplexSample (m := m) (n := 2)) :
    TwoColumnBlock m × TwoColumnBlock m :=
  euclideanGaussianSplit (twoColumnReindex m z)

theorem measurable_twoColumnSplit {m : ℕ} : Measurable (twoColumnSplit (m := m)) :=
  measurable_euclideanGaussianSplit.comp (twoColumnReindex m).continuous.measurable

theorem twoColumnSplit_apply {m : ℕ} (z : ComplexSample (m := m) (n := 2)) :
    twoColumnSplit z =
      (WithLp.toLp 2 (fun ik : Fin m × Fin 2 => z ((ik.1, 0), ik.2)),
       WithLp.toLp 2 (fun ik : Fin m × Fin 2 => z ((ik.1, 1), ik.2))) := by
  rfl

/-- The actual m-by-2 Gaussian sample splits into independent column laws. -/
theorem twoColumnSplit_law (m : ℕ) :
    (stdGaussian (ComplexSample (m := m) (n := 2))).map twoColumnSplit =
      (stdGaussian (TwoColumnBlock m)).prod (stdGaussian (TwoColumnBlock m)) := by
  change (stdGaussian (ComplexSample (m := m) (n := 2))).map
    (euclideanGaussianSplit ∘ twoColumnReindex m) = _
  rw [← Measure.map_map measurable_euclideanGaussianSplit (by fun_prop),
    stdGaussian_map, stdGaussian_sum_split]

/-- The inverse column assembly, used inside the second-column integral. -/
def twoColumnJoin {m : ℕ} (p : TwoColumnBlock m × TwoColumnBlock m) :
    ComplexSample (m := m) (n := 2) :=
  (twoColumnReindex m).symm (WithLp.toLp 2
    (Sum.elim (fun ik => p.1 ik) (fun ik => p.2 ik)))

theorem measurable_twoColumnJoin {m : ℕ} : Measurable (twoColumnJoin (m := m)) := by
  unfold twoColumnJoin
  apply (twoColumnReindex m).symm.continuous.measurable.comp
  apply (EuclideanSpace.equiv ((Fin m × Fin 2) ⊕ (Fin m × Fin 2)) ℝ).symm.continuous.measurable.comp
  apply measurable_pi_iff.mpr
  intro x
  cases x <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

theorem twoColumnJoin_split {m : ℕ} (z : ComplexSample (m := m) (n := 2)) :
    twoColumnJoin (twoColumnSplit z) = z := by
  unfold twoColumnJoin twoColumnSplit euclideanGaussianSplit
  have h : WithLp.toLp 2 (Sum.elim
      (fun ik => (WithLp.toLp 2 (fun i => twoColumnReindex m z (.inl i))) ik)
      (fun ik => (WithLp.toLp 2 (fun i => twoColumnReindex m z (.inr i))) ik)) =
      twoColumnReindex m z := by
    ext x
    cases x <;> rfl
  rw [h, LinearIsometryEquiv.symm_apply_apply]

theorem twoColumnSplit_join {m : ℕ} (p : TwoColumnBlock m × TwoColumnBlock m) :
    twoColumnSplit (twoColumnJoin p) = p := by
  unfold twoColumnSplit twoColumnJoin
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem twoColumnJoin_first_apply {m : ℕ} (u v : TwoColumnBlock m)
    (ik : Fin m × Fin 2) : twoColumnJoin (u, v) ((ik.1, 0), ik.2) = u ik := by
  have h := congrArg (fun p : TwoColumnBlock m × TwoColumnBlock m => p.1 ik)
    (twoColumnSplit_join (u, v))
  simpa only [twoColumnSplit_apply] using h

theorem twoColumnJoin_second_apply {m : ℕ} (u v : TwoColumnBlock m)
    (ik : Fin m × Fin 2) : twoColumnJoin (u, v) ((ik.1, 1), ik.2) = v ik := by
  have h := congrArg (fun p : TwoColumnBlock m × TwoColumnBlock m => p.2 ik)
    (twoColumnSplit_join (u, v))
  simpa only [twoColumnSplit_apply] using h

theorem twoColumnJoin_complex_first {m : ℕ} (u v : TwoColumnBlock m) (i : Fin m) :
    complexSampleMatrix (twoColumnJoin (u, v)) i 0 =
      ((u (i, 0) : ℂ) + Complex.I * u (i, 1)) / Real.sqrt 2 := by
  rw [complexSampleMatrix, twoColumnJoin_first_apply u v (i, 0),
    twoColumnJoin_first_apply u v (i, 1)]

theorem twoColumnJoin_complex_second {m : ℕ} (u v : TwoColumnBlock m) (i : Fin m) :
    complexSampleMatrix (twoColumnJoin (u, v)) i 1 =
      ((v (i, 0) : ℂ) + Complex.I * v (i, 1)) / Real.sqrt 2 := by
  rw [complexSampleMatrix, twoColumnJoin_second_apply u v (i, 0),
    twoColumnJoin_second_apply u v (i, 1)]

theorem twoColumnJoin_law (m : ℕ) :
    ((stdGaussian (TwoColumnBlock m)).prod (stdGaussian (TwoColumnBlock m))).map
      twoColumnJoin = stdGaussian (ComplexSample (m := m) (n := 2)) := by
  rw [← twoColumnSplit_law m,
    Measure.map_map measurable_twoColumnJoin measurable_twoColumnSplit]
  have hfun : twoColumnJoin ∘ twoColumnSplit =
      (id : ComplexSample (m := m) (n := 2) → ComplexSample) := funext twoColumnJoin_split
  rw [hfun, Measure.map_id]

/-- Tonelli on the actual m-by-2 sample: first column outside, second inside.
Nonnegative measurable tests avoid an unstated absolute-integrability premise. -/
theorem twoColumn_lintegral_eq_iterated (m : ℕ)
    (g : ComplexSample (m := m) (n := 2) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z, g z ∂stdGaussian (ComplexSample (m := m) (n := 2)) =
      ∫⁻ u, ∫⁻ v, g (twoColumnJoin (u, v))
        ∂stdGaussian (TwoColumnBlock m) ∂stdGaussian (TwoColumnBlock m) := by
  rw [← twoColumnJoin_law m, lintegral_map hg measurable_twoColumnJoin]
  exact lintegral_prod _ (hg.comp measurable_twoColumnJoin).aemeasurable

/-- A noncentral ordered-spectral event of the actual two-column model,
with no proposed Gram density, now has a first/second-column iterated integral. -/
theorem paperTwoColumnSpectrum_event_eq_iterated {m : ℕ}
    (M : Matrix (Fin m) (Fin 2) ℂ) (B : Set (Fin (min m 2) → ℝ))
    (hB : MeasurableSet B) :
    ((stdGaussian (ComplexSample (m := m) (n := 2))).map (paperJointSpectrum M)) B =
      ∫⁻ u, ∫⁻ v, ((paperJointSpectrum M) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞))
        (twoColumnJoin (u, v))
        ∂stdGaussian (TwoColumnBlock m) ∂stdGaussian (TwoColumnBlock m) := by
  have hs := hB.preimage (measurable_paperJointSpectrum M)
  rw [Measure.map_apply (measurable_paperJointSpectrum M) hB]
  have hi := lintegral_indicator_const (μ := stdGaussian (ComplexSample (m := m) (n := 2)))
    hs (c := (1 : ℝ≥0∞))
  simp only [one_mul] at hi
  rw [← hi]
  exact twoColumn_lintegral_eq_iterated m
    (((paperJointSpectrum M) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hs)

/-- A measurable first-column-dependent orthogonal change of the second column
preserves its joint Gaussian product law. This does not assume the direction
chosen from the first column is independent of it. -/
theorem twoColumn_gaussian_fiber_rotation (m : ℕ)
    (R : TwoColumnBlock m → TwoColumnBlock m ≃ₗᵢ[ℝ] TwoColumnBlock m)
    (hR : Measurable (fun p : TwoColumnBlock m × TwoColumnBlock m => R p.1 p.2)) :
    MeasurePreserving (fun p : TwoColumnBlock m × TwoColumnBlock m => (p.1, R p.1 p.2))
      ((stdGaussian (TwoColumnBlock m)).prod (stdGaussian (TwoColumnBlock m)))
      ((stdGaussian (TwoColumnBlock m)).prod (stdGaussian (TwoColumnBlock m))) := by
  exact (MeasurePreserving.id (stdGaussian (TwoColumnBlock m))).skew_product
    (μc := stdGaussian (TwoColumnBlock m)) (μd := stdGaussian (TwoColumnBlock m))
    (g := fun u v => R u v) hR
    (Filter.Eventually.of_forall (fun u => stdGaussian_map (R u)))

/-- The same rotating-frame statement on the actual matrix sample itself. -/
theorem twoColumn_rotated_split_law (m : ℕ)
    (R : TwoColumnBlock m → TwoColumnBlock m ≃ₗᵢ[ℝ] TwoColumnBlock m)
    (hR : Measurable (fun p : TwoColumnBlock m × TwoColumnBlock m => R p.1 p.2)) :
    (stdGaussian (ComplexSample (m := m) (n := 2))).map
      (fun z => ((twoColumnSplit z).1, R (twoColumnSplit z).1 (twoColumnSplit z).2)) =
      (stdGaussian (TwoColumnBlock m)).prod (stdGaussian (TwoColumnBlock m)) := by
  have hr := twoColumn_gaussian_fiber_rotation m R hR
  change (stdGaussian (ComplexSample (m := m) (n := 2))).map
    ((fun p : TwoColumnBlock m × TwoColumnBlock m => (p.1, R p.1 p.2)) ∘ twoColumnSplit) = _
  rw [← Measure.map_map hr.measurable measurable_twoColumnSplit,
    twoColumnSplit_law, hr.map_eq]

end

end JinWishart
