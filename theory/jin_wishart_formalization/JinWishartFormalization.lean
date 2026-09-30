import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import JinWishartFormalization.IncompleteGamma
import JinWishartFormalization.NuttallQ
import JinWishartFormalization.Theorem1Formula
import JinWishartFormalization.WishartProbability
import JinWishartFormalization.WishartGamma
import JinWishartFormalization.RadialIntegration
import JinWishartFormalization.GaussianRadialLaw
import JinWishartFormalization.GaussianRadialCDF
import JinWishartFormalization.MIMOPerformance
import JinWishartFormalization.GaussianQ
import JinWishartFormalization.MIMOWishartSER
import JinWishartFormalization.BesselI0Series
import JinWishartFormalization.BesselI0Angle
import JinWishartFormalization.NoncentralScalarCDF
import JinWishartFormalization.NuttallQZero
import JinWishartFormalization.ScalarNoncentralPolar
import JinWishartFormalization.ScalarAngularRadial
import JinWishartFormalization.ScalarNoncentralDiskFubini
import JinWishartFormalization.ScalarComplexCenterAngle
import JinWishartFormalization.ScalarGaussianComplexBridge
import JinWishartFormalization.NuttallQRiceSplit
import JinWishartFormalization.Theorem1FullRankDeterminantScaling
import JinWishartFormalization.ScalarComplexCenterDisk
import JinWishartFormalization.ScalarNoncentralCDFRice
import JinWishartFormalization.ScalarNoncentralNoAtom
import JinWishartFormalization.NuttallQRiceMass
import JinWishartFormalization.NuttallQRiceNormalization
import JinWishartFormalization.ScalarNoncentralTheorem1
import JinWishartFormalization.Theorem2NoncentralScalarFormula
import JinWishartFormalization.OrderedEigenvalueCDFRecurrence
import JinWishartFormalization.OneColumnNoAtom
import JinWishartFormalization.BesselI1Series
import JinWishartFormalization.Theorem1SingleColumnTwoRows
import JinWishartFormalization.OneColumnCDFRecurrence
import JinWishartFormalization.Theorem1SingleColumnAnyRows
import JinWishartFormalization.Theorem1ThreeRowsActualCDF
import JinWishartFormalization.NoncentralFourDimensionalRadial
import JinWishartFormalization.OrderedEigenvalueStrictRecurrence
import JinWishartFormalization.OrderedEigenvalueIndexedRecurrence
import JinWishartFormalization.ScalarNoncentralSmallX
import JinWishartFormalization.WeightedIntervalAverage
import JinWishartFormalization.ScalarNoncentralSmallXLimit
import JinWishartFormalization.Theorem2SingleColumnAnyRows
import JinWishartFormalization.Theorem2ThreeRowsActualCDF
import JinWishartFormalization.BesselI1Angle
import JinWishartFormalization.NoncentralFourDimensionalSphere
import JinWishartFormalization.NoncentralFourDimensionalTail
import JinWishartFormalization.NuttallQ21Positive
import JinWishartFormalization.Theorem1TwoRowsNoncentral
import JinWishartFormalization.FourDimensionalPolarBridge
import JinWishartFormalization.ScalarNoncentralOutageAsymptotic
import JinWishartFormalization.NoncentralFourDimensionalPoissonMixture
import JinWishartFormalization.OrderedEigenvalueMeasurable
import JinWishartFormalization.OrderedEigenvalueWeyl
import JinWishartFormalization.SubspaceIntersectionFinrank
import JinWishartFormalization.IndexedCourantFischerAttempt
import JinWishartFormalization.IndexedCourantFischerProof
import JinWishartFormalization.WeylRealSymmetric
import JinWishartFormalization.WeylComplexHermitian
import JinWishartFormalization.OrderedEigenvalueFullMeasurable
import JinWishartFormalization.DeterminantRowExpansion
import JinWishartFormalization.T3FixedCardinalityRowSelection
import JinWishartFormalization.T3PaperThetaSpecialization
import JinWishartFormalization.T3NormalizationAudit
import JinWishartFormalization.T3InactiveColumnCancellation
import JinWishartFormalization.RepeatedRootNullSets
import JinWishartFormalization.MvPolynomialZeroSetNull
import JinWishartFormalization.MvPolynomialGramTwoByTwo
import JinWishartFormalization.RealQuadraticRepeatedRoot
import JinWishartFormalization.ComplexGramTwoByTwoDiscriminantNull
import JinWishartFormalization.PaperSmallSideGram
import JinWishartFormalization.PaperSingleStreamTwoRowOutage
import JinWishartFormalization.T4CentralOneColumnAnyRows
import JinWishartFormalization.T4CentralOneColumnHighScale
import JinWishartFormalization.T4DensityToCDF
import JinWishartFormalization.SpectralRayleighCoordinates
import JinWishartFormalization.SpectralRayleighPrefix
import JinWishartFormalization.NuttallQ21Normalization
import JinWishartFormalization.ScalarPhysicalScaling
import JinWishartFormalization.NoncentralOneColumnEnergy
import JinWishartFormalization.SphereThreeMeasure
import JinWishartFormalization.GaussianEuclideanBallDensity
import JinWishartFormalization.SphereFourDAngularIntegral
import JinWishartFormalization.SphereFourDPlanePolar
import JinWishartFormalization.SphereFourDPlaneAngleChart
import JinWishartFormalization.NoncentralFourDimensionalCDF
import JinWishartFormalization.NoncentralFourDimensionalGaussianCDF
import JinWishartFormalization.SixDimensionalAngularBesselI2
import JinWishartFormalization.EightDimensionalAngularBesselI3
import JinWishartFormalization.SphereEightDAxialMeasure
import JinWishartFormalization.SphereSixDAxialMeasure
import JinWishartFormalization.NoncentralSixDimensionalRadial
import JinWishartFormalization.NoncentralEightDimensionalRadial
import JinWishartFormalization.ThreeRowSampleCoordinates
import JinWishartFormalization.ThreeRowMeanNorm
import JinWishartFormalization.NoncentralSixDimensionalMass
import JinWishartFormalization.NoncentralThreeRowNuttallQ
import JinWishartFormalization.TwoRowSampleCoordinates
import JinWishartFormalization.TwoRowMeanGramSpectrum
import JinWishartFormalization.Theorem1TwoRowsActualCDF
import JinWishartFormalization.TwoRowSmallOutageAsymptotic
import JinWishartFormalization.TwoRowOutageScaling
import JinWishartFormalization.WishartSimpleSpectrum
import JinWishartFormalization.ComplexGramTwoByTwoGaussianSimpleSpectrum
import JinWishartFormalization.Theorem12ThreeRowsFrobeniusCDF
import JinWishartFormalization.FinSpectralIndexCard
import JinWishartFormalization.MIMOWishartSERExact
import JinWishartFormalization.PaperStatements
import JinWishartFormalization.ComplexGramSimpleSpectrum
import JinWishartFormalization.GramSpectrumTransfer
import JinWishartFormalization.RectangularGramEigenvectorBridge
import JinWishartFormalization.ThresholdNoAtom
import JinWishartFormalization.NuttallQBoundary
import JinWishartFormalization.NoncentralEvenDimensionalPoissonMixture
import JinWishartFormalization.T3CentralTwoByTwoDensityInterface
import JinWishartFormalization.OneColumnFrobeniusParameter

/-!
# A Lean feasibility prototype for Jin--McKay--Gao--Collings (2008)

This file formalizes self-contained algebraic and analytic consequences used in
"MIMO Multichannel Beamforming: SER and Outage Using New Eigenvalue
Distributions of Complex Noncentral Wishart Matrices" (arXiv:cs/0611007).

It deliberately does **not** claim to formalize the paper's new Wishart
eigenvalue-distribution theorems.  See `README.md` for the exact scope.
-/

namespace JinWishart

open Real

/-- The complete descending eigenvalue vector of an actual shifted complex
Gaussian Gram sample is measurable in every finite dimension. -/
theorem measurable_complexNoncentralSampleEigenvalueVector
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (fun z : ComplexSample (m := m) (n := n) =>
      fun i => complexNoncentralSampleEigenvalue M i z) := by
  exact measurable_complexNoncentralSampleEigenvalueVector_of_continuous M
    (orderedHermitianEigenvalueCoordinatesContinuous n)

/-- The complete ordered spectrum of the paper's smaller-side Gram matrix is
measurable for every rectangular noncentral complex Gaussian sample. -/
theorem measurable_paperSmallSideSampleEigenvalueVector
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (fun z : ComplexSample (m := m) (n := n) =>
      fun i =>
        (paperSmallSideGram_posSemidef (complexSampleMatrix z + M)).1.eigenvalues₀ i) := by
  rw [measurable_pi_iff]
  intro i
  let G : ComplexSample (m := m) (n := n) → HermitianMatrix (min m n) := fun z =>
    ⟨paperSmallSideGram (complexSampleMatrix z + M),
      (paperSmallSideGram_posSemidef (complexSampleMatrix z + M)).1⟩
  have hG : Measurable G := by
    exact (measurable_shiftedPaperSmallSideGram M).subtype_mk
      (h := fun z => (paperSmallSideGram_posSemidef
        (complexSampleMatrix z + M)).1)
  change Measurable
    ((fun A : HermitianMatrix (min m n) => hermitianEigenvalueVector A i) ∘ G)
  exact (orderedHermitianEigenvalueCoordinatesContinuous (min m n) i).measurable.comp hG

/-- The Rice-factor term in the leading low-outage approximation, with the
integer exponent `n = s * t` abstracted as a natural number. -/
noncomputable def riceFactor (n : ℕ) (K : ℝ) : ℝ :=
  (K + 1) ^ n * Real.exp (-(K * n))

/-- Equation (45) of the paper: the derivative of the Rice-factor term. -/
theorem hasDerivAt_riceFactor (n : ℕ) (K : ℝ) :
    HasDerivAt (riceFactor n)
      (-(n : ℝ) * K * (K + 1) ^ (n - 1) * Real.exp (-(K * n))) K := by
  cases n with
  | zero =>
      convert (hasDerivAt_const (x := K) (c := (1 : ℝ))) using 1
      · funext x
        norm_num [riceFactor]
      · norm_num
  | succ n =>
      have hpow :
            HasDerivAt (fun x : ℝ => (x + 1) ^ (n + 1))
            ((n + 1 : ℕ) * (K + 1) ^ n) K := by
        convert ((hasDerivAt_id K).add_const 1).pow (n + 1) using 1
        · funext x
          simp
        · push_cast
          simp [id]
      have hinner :
          HasDerivAt (fun x : ℝ => -(x * (n + 1 : ℕ))) (-(n + 1 : ℕ)) K := by
        convert ((hasDerivAt_id K).mul_const (n + 1 : ℕ)).neg using 1
        · funext x
          simp
        · push_cast
          ring
      have hexp :
          HasDerivAt (fun x : ℝ => Real.exp (-(x * (n + 1 : ℕ))))
            (Real.exp (-(K * (n + 1 : ℕ))) * (-(n + 1 : ℕ))) K :=
        (Real.hasDerivAt_exp _).comp K hinner
      convert hpow.mul hexp using 1
      · funext x
        simp only [riceFactor, Nat.cast_add, Nat.cast_one, Pi.mul_apply]
      · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
        ring

/-- For a nonzero antenna product and positive Rice factor, the derivative in
Equation (45) is strictly negative.  This is the local monotonicity statement
behind the paper's low-outage conclusion. -/
theorem riceFactor_derivative_neg {n : ℕ} {K : ℝ}
    (hn : 0 < n) (hK : 0 < K) :
    -(n : ℝ) * K * (K + 1) ^ (n - 1) * Real.exp (-(K * n)) < 0 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hbase : 0 < K + 1 := by linarith
  have hpow : 0 < (K + 1) ^ (n - 1) := pow_pos hbase _
  have hexp : 0 < Real.exp (-(K * n)) := Real.exp_pos _
  have hprod :
      0 < (n : ℝ) * K * (K + 1) ^ (n - 1) * Real.exp (-(K * n)) := by
    positivity
  nlinarith

/-- For a nonzero antenna product, the Rice-factor term is strictly decreasing
on the physically relevant region `K > 0`.  This packages the derivative-sign
calculation into the monotonicity conclusion used after Equation (45). -/
theorem riceFactor_strictAntiOn {n : ℕ} (hn : 0 < n) :
    StrictAntiOn (riceFactor n) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact (continuous_iff_continuousAt.mpr fun K =>
      (hasDerivAt_riceFactor n K).continuousAt).continuousOn
  · intro K hK
    rw [(hasDerivAt_riceFactor n K).deriv]
    exact riceFactor_derivative_neg hn (by simpa using hK)

/-- The normalized high-SNR outage coefficient in the paper's actual `2 × 1`,
single-stream specialization. -/
noncomputable def paperTwoRowOutageCoefficient (γ K : ℝ) : ℝ :=
  (K + 1) ^ 2 * γ ^ 2 * (1 / 2) * Real.exp (-2 * K)

theorem paperTwoRowOutageCoefficient_eq_riceFactor (γ K : ℝ) :
    paperTwoRowOutageCoefficient γ K = (γ ^ 2 / 2) * riceFactor 2 K := by
  simp [paperTwoRowOutageCoefficient, riceFactor]
  ring

/-- For every positive threshold, the `2 × 1`, single-stream low-outage
coefficient strictly decreases with the Rice factor, matching (45) in this
special case. -/
theorem paperTwoRowOutageCoefficient_strictAntiOn (γ : ℝ) (hγ : 0 < γ) :
    StrictAntiOn (paperTwoRowOutageCoefficient γ) (Set.Ioi 0) := by
  intro K hK L hL hKL
  rw [paperTwoRowOutageCoefficient_eq_riceFactor,
    paperTwoRowOutageCoefficient_eq_riceFactor]
  exact mul_lt_mul_of_pos_left
    (riceFactor_strictAntiOn (n := 2) (by norm_num) hK hL hKL)
    (by positivity)

/-- A finite Gram energy is nonnegative.  In the MIMO model this is the
coordinate form of `xᴴ Hᴴ H x = ‖Hx‖² ≥ 0`, the deterministic fact behind the
nonnegative eigenmode gains of a Wishart/Gram matrix. -/
theorem gram_energy_nonneg {m n : ℕ}
    (H : Fin m → Fin n → ℂ) (x : Fin n → ℂ) :
    0 ≤ ∑ i, ‖∑ j, H i j * x j‖ ^ 2 := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- With equal nonnegative power/scaling, an ordered weakest eigenmode has the
smallest SNR.  This isolates the order argument used when the paper says the
weakest active subchannel dominates high-SNR error/outage. -/
theorem weakest_mode_has_smallest_snr
    {φweak φ : ℝ} {scale power : ℝ}
    (hφ : φweak ≤ φ) (hscale : 0 ≤ scale) (hpower : 0 ≤ power) :
    scale * φweak * power ≤ scale * φ * power := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hφ hscale) hpower

end JinWishart
