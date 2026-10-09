import JinWishartFormalization.T3CentralNormalizationWitness

open JinWishart

#print axioms theorem3CentralTwoThree_at_two
#print axioms theorem3CentralTwoThree_at_two_gt_one

-- Explicit row selections only: the generic powerset-sum bridge remains open.
example : 1 < centralTwoThreeMixedRowSum.re :=
  theorem3CentralTwoThree_at_two_gt_one

example : theorem3C3 2 3 0 (by decide) emptyNoncentralSpectrum = 1 := by
  norm_num [theorem3C3, theorem3GammaFactor]
  change (∏ x : Fin 2, (Nat.factorial (1 - x.val) : ℝ)) = 1
  rw [Fin.prod_univ_two]
  norm_num
