import JinWishartFormalization.TwoRowGramChart

/-!
# Positive Bartlett chart image

Deterministic support-domain algebra for the next actual density bridge.
The local DeepSeek attempts and orchestration contributions are recorded in
notes/DEEPSEEK_WISHART_PROGRESS_20261010.md.
This is not an almost-sure support statement or a probability density theorem.
[需人工审查] Interpretation as the actual Hermitian Gram support and density boundaries.
-/

open MeasureTheory

namespace JinWishart
noncomputable section

theorem twoRowGramChart_right_inverse (q : GramChartSpace) (hq : 0 < q 0) :
    twoRowGramChart (twoRowGramChartInverse q) = q := by
  have hn : Real.sqrt (q 0) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  ext i
  fin_cases i <;> simp [twoRowGramChart, twoRowGramChartInverse] <;> field_simp [hn]

theorem twoRowGramChart_determinant (p : GramChartSpace) (hp : 0 < p 0) :
    twoRowGramChart p 0 * twoRowGramChart p 3 -
      (twoRowGramChart p 1) ^ 2 - (twoRowGramChart p 2) ^ 2 = p 0 * p 3 := by
  simp [twoRowGramChart, mul_pow, Real.sq_sqrt (le_of_lt hp)]
  <;> ring

theorem twoRowGramChart_inverse_residual_pos (q : GramChartSpace)
    (hq : 0 < q 0) (hd : q 1 ^ 2 + q 2 ^ 2 < q 0 * q 3) :
    0 < twoRowGramChartInverse q 3 := by
  have hp : 0 < twoRowGramChartInverse q 0 := by
    simpa [twoRowGramChartInverse] using hq
  have hdet := twoRowGramChart_determinant (twoRowGramChartInverse q) hp
  rw [twoRowGramChart_right_inverse q hq] at hdet
  have hprod : 0 < q 0 * twoRowGramChartInverse q 3 := by
    simpa only [twoRowGramChartInverse, Matrix.cons_val_zero] using
      (show 0 < twoRowGramChartInverse q 0 * twoRowGramChartInverse q 3 from by
        nlinarith [hd])
  exact (mul_pos_iff_of_pos_left hq).mp hprod

theorem twoRowGramChart_positive_image :
    twoRowGramChart '' {p : GramChartSpace | 0 < p 0 ∧ 0 < p 3} =
      {q : GramChartSpace | 0 < q 0 ∧ q 1 ^ 2 + q 2 ^ 2 < q 0 * q 3} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨by simpa [twoRowGramChart] using hp.1, ?_⟩
    have hdet := twoRowGramChart_determinant p hp.1
    have hpos := mul_pos hp.1 hp.2
    nlinarith
  · intro hq
    exact ⟨twoRowGramChartInverse q,
      ⟨by simpa [twoRowGramChartInverse] using hq.1,
        twoRowGramChart_inverse_residual_pos q hq.1 hq.2⟩,
      twoRowGramChart_right_inverse q hq.1⟩

end
end JinWishart
