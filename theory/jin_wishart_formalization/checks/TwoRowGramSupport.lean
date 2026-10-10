import JinWishartFormalization.TwoRowGramSupport

open JinWishart

#print axioms twoRowGramChart_right_inverse
#print axioms twoRowGramChart_determinant
#print axioms twoRowGramChart_inverse_residual_pos
#print axioms twoRowGramChart_positive_image

-- Positive, zero and negative residuals correspond to the three determinant signs.
example : twoRowGramChart ![1, 2, 3, 4] = ![1, 2, 3, 17] := by
  ext i
  fin_cases i <;> norm_num [twoRowGramChart]

example : ¬ (0 < (twoRowGramChart ![1, 2, 3, 0]) 0 ∧
    (twoRowGramChart ![1, 2, 3, 0]) 1 ^ 2 +
      (twoRowGramChart ![1, 2, 3, 0]) 2 ^ 2 <
      (twoRowGramChart ![1, 2, 3, 0]) 0 * (twoRowGramChart ![1, 2, 3, 0]) 3) := by
  norm_num [twoRowGramChart]

example : ¬ (0 < (twoRowGramChart ![1, 2, 3, -2]) 0 ∧
    (twoRowGramChart ![1, 2, 3, -2]) 1 ^ 2 +
      (twoRowGramChart ![1, 2, 3, -2]) 2 ^ 2 <
      (twoRowGramChart ![1, 2, 3, -2]) 0 * (twoRowGramChart ![1, 2, 3, -2]) 3) := by
  norm_num [twoRowGramChart]
