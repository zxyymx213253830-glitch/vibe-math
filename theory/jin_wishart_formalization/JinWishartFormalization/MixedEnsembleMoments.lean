import JinWishartFormalization.MixedEnsembleSign
import JinWishartFormalization.MixedKernelMoments
import JinWishartFormalization.MixedNoncentralMomentMatrix

/-! Codex. Seeds 2026103003/3004 scalar and matrix quadrature controls precede
source. The moment matrix is formula-side; actual Wishart law remains open.
[需人工审查] Restriction to positive t, Fubini, indices and model mapping. -/
open MeasureTheory Matrix Finset Set
namespace JinWishart
noncomputable section

theorem mixedEnsemble_pair_moment (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j) (i j : Fin (p+L)) :
 IntegrableOn (fun t => mixedEnsembleF p L i t * mixedEnsembleG p L q lambda j t) (Ioi 0) ∧
 (∫ t in Ioi (0 : ℝ), mixedEnsembleF p L i t * mixedEnsembleG p L q lambda j t) =
   match (finSumFinEquiv (m := p) (n := L)).symm j with
   | Sum.inl a => ((q+i.val+a.val).factorial : ℝ)
   | Sum.inr b => Real.exp (lambda b)*poissonFactorialMomentPolynomial q i.val (lambda b) := by
 cases hj : (finSumFinEquiv (m := p) (n := L)).symm j with
 | inl a =>
   have he (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
     mixedEnsembleF p L i t * mixedEnsembleG p L q lambda j t =
       t^(q+i.val+a.val)*Real.exp (-t) := by
     have ht0 : 0 < t := ht
     simp only [mixedEnsembleF,mixedEnsembleG,if_pos ht0,hj]
     simp only [pow_add]
     ring
   have base := integral_natPower_exp_neg_Ioi (q+i.val+a.val)
   constructor
   · exact (integrableOn_congr_fun he measurableSet_Ioi).2 base.1
   · rw [setIntegral_congr_fun measurableSet_Ioi he,base.2]
 | inr b =>
   have he (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
     mixedEnsembleF p L i t * mixedEnsembleG p L q lambda j t =
       t^(q+i.val)*Real.exp (-t)*scalarSeriesKernel q (lambda b) t := by
     have ht0 : 0 < t := ht
     simp only [mixedEnsembleF,mixedEnsembleG,if_pos ht0,hj,scalarSeriesKernel,pow_add]
     ring
   have base := scalarSeriesKernel_weightedMoment q i.val (lambda b) (hl b)
   constructor
   · exact (integrableOn_congr_fun he measurableSet_Ioi).2 base.1
   · rw [setIntegral_congr_fun measurableSet_Ioi he,base.2]

def mixedEnsembleColumnFactor (p L : ℕ) (lambda : Fin L → ℝ) : Fin p ⊕ Fin L → ℝ
 | Sum.inl _ => 1
 | Sum.inr b => Real.exp (lambda b)

theorem mixedEnsemble_momentMatrix_eq (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j) :
 determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ))) (mixedEnsembleF p L)
   (mixedEnsembleG p L q lambda) =
 (Matrix.of (fun i j => mixedEnsembleColumnFactor p L lambda j *
   mixedNoncentralMomentMatrix q p L lambda i j)).submatrix
     (finSumFinEquiv (m := p) (n := L)).symm (finSumFinEquiv (m := p) (n := L)).symm := by
 ext i j
 have h := (mixedEnsemble_pair_moment p L q lambda hl i j).2
 change (∫ t in Ioi (0 : ℝ), mixedEnsembleF p L i t * mixedEnsembleG p L q lambda j t) = _
 rw [h]
 cases hj : (finSumFinEquiv (m := p) (n := L)).symm j with
 | inl a =>
   simp [hj,mixedEnsembleColumnFactor,mixedNoncentralMomentMatrix,mixedMomentDegree]
 | inr b =>
   simp [hj,mixedEnsembleColumnFactor,mixedNoncentralMomentMatrix,mixedMomentDegree]

theorem mixedEnsemble_momentMatrix_det_pos (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) :
 0 < (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ))) (mixedEnsembleF p L)
   (mixedEnsembleG p L q lambda)).det := by
 rw [mixedEnsemble_momentMatrix_eq p L q lambda (fun j => (hlp j).le),
   Matrix.det_submatrix_equiv_self,Matrix.det_mul_row,mixedNoncentralMomentMatrix_det]
 have hv : 0 < (∏ j : Fin L, lambda j^p)*(Matrix.vandermonde lambda).det := by
   rw [← zeroConfluentVandermonde_det]
   exact zeroConfluentVandermonde_det_pos p L lambda hl hlp
 have hg : 0 < ∏ h : Fin p, (h.val.factorial : ℝ)*((q+h.val).factorial : ℝ) := by
   apply Finset.prod_pos
   intro i hi
   positivity
 have hc : 0 < ∏ j : Fin p ⊕ Fin L, mixedEnsembleColumnFactor p L lambda j := by
   apply Finset.prod_pos
   intro j hj
   cases j with
   | inl a => simp [mixedEnsembleColumnFactor]
   | inr b => exact Real.exp_pos _
 exact mul_pos hc (mul_pos hv hg)

end
end JinWishart
#print axioms JinWishart.mixedEnsemble_pair_moment
#print axioms JinWishart.mixedEnsemble_momentMatrix_eq
#print axioms JinWishart.mixedEnsemble_momentMatrix_det_pos
