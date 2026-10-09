import JinWishartFormalization.T3ScalarNormalizationBridge

open JinWishart

private def centralSpectrum : OrderedPositiveNoncentralSpectrum 0 where
  values := Fin.elim0
  positive := fun i => Fin.elim0 i
  strictAnti := fun i => Fin.elim0 i

-- These constants were wrong by factors of four or larger with multiplication.
example : theorem3C3 3 4 0 (by omega) centralSpectrum = (1 / 2 : ℝ) := by
  norm_num [theorem3C3, theorem3GammaFactor, Fin.prod_univ_succ]

-- Displayed and density-derived constants intentionally remain different.
example : theorem3DerivedC3 2 3 0 (by omega) centralSpectrum = (1 / 2 : ℝ) := by
  norm_num [theorem3DerivedC3, theorem3C3, theorem3GammaFactor,
    T3NormalizationAudit.factorialMultigamma, Fin.prod_univ_succ]

example : theorem3C3 2 3 0 (by omega) centralSpectrum = (1 : ℝ) := by
  norm_num [theorem3C3, theorem3GammaFactor, Fin.prod_univ_succ]

#print axioms theorem3C3_eq_auditedScalar
#print axioms theorem3_densityColumnFactors_eq_derivedC3
#print axioms theorem3DerivedC3_fullRank
