import JinWishartFormalization.OneColumnRadialCDF
import JinWishartFormalization.FourRowSampleCoordinates
import JinWishartFormalization.OneColumnFrobeniusParameter

/-! Original T1/T2 candidates for the actual properCN1 four-row one-column
sample with arbitrary fixed nonzero complex mean. Codex. Seed2026102250
234 calibrated controls precede source. Reuses the existing E8 actual lower
radial law; no Gaussian coordinate/angle integration is repeated.
[需人工审查] Inherited E8 measure/rotation, Frobenius convention and paper mapping. -/
open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem theorem12FourRowsCandidates_eq_actualCDF_frobenius
    (M : Matrix (Fin 4) (Fin 1) ℂ) (x : ℝ)
    (hEnergy : 0<∑ i : Fin 4,‖M i 0‖^2) (hx : 0≤x) :
    let lambda := ∑ i : Fin 4,‖M i 0‖^2
    let F := cdf ((stdGaussian (ComplexSample (m := 4) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x
    theorem1CdfCandidate 1 4 1 (by omega) (by omega) (fun _ : Fin 1 => lambda) x=F ∧
      theorem2CdfCandidate 1 4 1 (by omega) (by omega) (fun _ : Fin 1 => lambda) x=F := by
  intro lambda F
  have h := theorem12OneColumnCandidates_eq_radialCDF 4 (by omega) lambda x hEnergy hx
  have hnorm : ‖fourRowSampleToFin8 (complexSampleMean M)‖=Real.sqrt (2*lambda) := by
    have hs : ‖fourRowSampleToFin8 (complexSampleMean M)‖^2=2*lambda := by
      rw [fourRowSampleToFin8.norm_map]
      exact complexSampleMean_oneColumn_norm_sq_eq_twice_frobenius M
    rw [← hs,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have hF : F=∫ r in Set.Ioc (0 : ℝ) (Real.sqrt (2*x)),
      noncentralChiEvenRadialKernel 3 (Real.sqrt (2*lambda)) r := by
    dsimp only [F]
    rw [noncentralFourRowCDF_eq_radialSeries_of_mean M x hx,hnorm]
  exact ⟨h.1.trans hF.symm,h.2.trans hF.symm⟩

end
end JinWishart
#print axioms JinWishart.theorem12FourRowsCandidates_eq_actualCDF_frobenius
