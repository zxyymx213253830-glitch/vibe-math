import JinWishartFormalization.IncompleteGamma

/-! Codex. Seed 2026103006 Nuttall/Gamma controls precede source.
Finite natural Gamma tail as a real scalar moment; no model law asserted.
[需人工审查] Improper integral and complex/real coercions. -/
open MeasureTheory Set
namespace JinWishart
noncomputable section

theorem upperGammaNat_eq_realTailMoment (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
 upperGammaNat k x = ((∫ y in Ioi x, y^k*Real.exp (-y) : ℝ) : ℂ) := by
 rw [upperGammaNat,upperGammaComplement_eq_tail (by norm_num <;> positivity) hx,upperGammaTail]
 have hfun : (fun y : ℝ => (Real.exp (-y) : ℂ)*(y : ℂ)^(((k+1 : ℕ) : ℂ)-1)) =
     fun y => ((y^k*Real.exp (-y) : ℝ) : ℂ) := by
   funext y
   rw [show ((k+1 : ℕ) : ℂ)-1=(k : ℂ) by push_cast; ring,Complex.cpow_natCast]
   push_cast
   ring
 rw [hfun,integral_complex_ofReal]

end
end JinWishart
#print axioms JinWishart.upperGammaNat_eq_realTailMoment
