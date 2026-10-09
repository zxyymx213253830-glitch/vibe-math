import JinWishartFormalization.T3PaperThetaSpecialization
import JinWishartFormalization.T3NormalizationAudit

/-!
# T3 scalar source alignment and the separate derived normalization

The displayed c3 uses division, not multiplication. This bridge identifies
the formula-side definition with the independent scalar audit. The extra
inactive-column Gamma factor is kept in a separate derived constant: it is
not silently inserted into the transcription of the paper's displayed c3.
No joint density or probability identity is asserted here.
-/

namespace JinWishart

noncomputable section

theorem theorem3GammaFactor_eq_factorialMultigamma (n : ℕ) :
    theorem3GammaFactor n = T3NormalizationAudit.factorialMultigamma n n := by
  rfl

/-- The paper transcription and scalar audit now encode exactly the same c3. -/
theorem theorem3C3_eq_auditedScalar
    (s t L : ℕ) (hLs : L ≤ s) (spectrum : OrderedPositiveNoncentralSpectrum L) :
    theorem3C3 s t L hLs spectrum =
      T3NormalizationAudit.paperC3 s t L spectrum.values := by
  rfl

/-- Scalar obtained by factoring all columns in the integrated density.
This is distinct from the paper's displayed constant until the residual
factor is one; no claim that it already equals an actual probability. -/
def theorem3DerivedC3
    (s t L : ℕ) (hLs : L ≤ s) (spectrum : OrderedPositiveNoncentralSpectrum L) : ℝ :=
  theorem3C3 s t L hLs spectrum /
    T3NormalizationAudit.factorialMultigamma (s - L) (t - L)

/-- Actual algebraic factorization, using the validated spectrum rather than
leaving positivity/distinctness as separate undocumented assumptions. -/
theorem theorem3_densityColumnFactors_eq_derivedC3
    (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (spectrum : OrderedPositiveNoncentralSpectrum L) :
    T3NormalizationAudit.paperC1 s t L spectrum.values *
        T3NormalizationAudit.paperColumnFactorProduct s t L spectrum.values =
      theorem3DerivedC3 s t L hLs spectrum := by
  rw [theorem3DerivedC3, theorem3C3_eq_auditedScalar]
  apply T3NormalizationAudit.paperC1_mul_columnFactors_eq_paperC3_div_inactiveGamma
    s t L hst hLs spectrum.values spectrum.positive
  intro i j hij
  exact ne_of_gt (spectrum.strictAnti hij)

/-- Full noncentral rank has no inactive columns and hence no residual factor. -/
theorem theorem3DerivedC3_fullRank
    (s t : ℕ) (spectrum : OrderedPositiveNoncentralSpectrum s) :
    theorem3DerivedC3 s t s (le_refl s) spectrum =
      theorem3C3 s t s (le_refl s) spectrum := by
  simp [theorem3DerivedC3, T3NormalizationAudit.factorialMultigamma]

end

end JinWishart
