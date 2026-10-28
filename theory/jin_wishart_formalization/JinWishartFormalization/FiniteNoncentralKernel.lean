import JinWishartFormalization.GeneralizedMonomialMinorProduct
import JinWishartFormalization.AveragedCauchyBinet

/-! Codex. Seed2026102801:171 exact finite-kernel/fixed-floor controls precede
source; older averaged Cauchy-Binet and minor-product controls are dependencies.
Full noncentral-rank finite series only. A fixed positive minor gives a floor
independent of the truncation length. No infinite kernel or actual joint law.
[需人工审查] All-function factorial multiplicity, minor orientation and limits. -/
open Matrix Finset Function
namespace JinWishart
noncomputable section

private theorem real_factorial_cauchy_binet {n N : ℕ}
 (A : Matrix (Fin n) (Fin N) ℝ) (B : Matrix (Fin N) (Fin n) ℝ) :
 (n.factorial : ℝ)*(A*B).det =
   ∑ f : Fin n → Fin N, (A.submatrix id f).det*(B.submatrix f id).det := by
 let AC : Matrix (Fin n) (Fin N) ℂ := A.map Complex.ofRealHom
 let BC : Matrix (Fin N) (Fin n) ℂ := B.map Complex.ofRealHom
 have h := det_mul_rectangular_factorial_sum_functions AC BC
 have hm : AC*BC = Complex.ofRealHom.mapMatrix (A*B) := by
   exact Matrix.map_mul.symm
 have hA (f : Fin n → Fin N) : AC.submatrix id f =
     Complex.ofRealHom.mapMatrix (A.submatrix id f) := rfl
 have hB (f : Fin n → Fin N) : BC.submatrix f id =
     Complex.ofRealHom.mapMatrix (B.submatrix f id) := rfl
 rw [hm,← Complex.ofRealHom.map_det] at h
 simp only [hA,hB,← Complex.ofRealHom.map_det] at h
 simpa [Complex.mul_re] using congrArg Complex.re h

def noncentralKernelSeriesWeight (q m : ℕ) : ℝ :=
 ((m.factorial : ℝ)*((q+m).factorial : ℝ))⁻¹

def finiteNoncentralFullKernel (q n N : ℕ) (x lambda : Fin n → ℝ) :
 Matrix (Fin n) (Fin n) ℝ :=
 Matrix.of (fun i j => ∑ m : Fin N,
   x i ^ m.val * (noncentralKernelSeriesWeight q m.val * lambda j ^ m.val))

def noncentralKernelLowestMinor (q n : ℕ) (x lambda : Fin n → ℝ) : ℝ :=
 (Matrix.of (fun i j : Fin n => x i ^ j.val)).det *
   (Matrix.of (fun i j : Fin n => noncentralKernelSeriesWeight q i.val * lambda j ^ i.val)).det

private theorem seriesWeight_pos (q m : ℕ) : 0 < noncentralKernelSeriesWeight q m := by
 unfold noncentralKernelSeriesWeight
 positivity

theorem finiteNoncentralFullKernel_det_lower_bound (q n N : ℕ) (hN : n ≤ N)
 (x lambda : Fin n → ℝ) (hx : StrictMono x) (hl : StrictMono lambda)
 (hxp : ∀ i, 0 < x i) (hlp : ∀ i, 0 < lambda i) :
 noncentralKernelLowestMinor q n x lambda ≤
   (n.factorial : ℝ)*(finiteNoncentralFullKernel q n N x lambda).det := by
 let A : Matrix (Fin n) (Fin N) ℝ := Matrix.of (fun i m => x i ^ m.val)
 let B : Matrix (Fin N) (Fin n) ℝ := Matrix.of (fun m j =>
   noncentralKernelSeriesWeight q m.val * lambda j ^ m.val)
 have hK : finiteNoncentralFullKernel q n N x lambda = A*B := by
   ext i j
   rfl
 rw [hK,real_factorial_cauchy_binet]
 let f0 : Fin n → Fin N := Fin.castLE hN
 have h0 : (A.submatrix id f0).det*(B.submatrix f0 id).det =
     noncentralKernelLowestMinor q n x lambda := by
   rfl
 rw [← h0]
 have hnonneg (f : Fin n → Fin N) : 0 ≤
     (A.submatrix id f).det*(B.submatrix f id).det := by
   have h := weightedGeneralizedMonomialMinorProduct_nonneg n (fun i => (f i).val)
     x lambda (fun i => noncentralKernelSeriesWeight q (f i).val) hx hl hxp hlp
       (fun i => seriesWeight_pos q (f i).val)
   convert h using 1 <;> rfl
 exact Finset.single_le_sum (f := fun f : Fin n → Fin N =>
   (A.submatrix id f).det*(B.submatrix f id).det) (fun f _ => hnonneg f) (Finset.mem_univ f0)

theorem finiteNoncentralFullKernel_det_pos (q n N : ℕ) (hN : n ≤ N)
 (x lambda : Fin n → ℝ) (hx : StrictMono x) (hl : StrictMono lambda)
 (hxp : ∀ i, 0 < x i) (hlp : ∀ i, 0 < lambda i) :
 0 < (finiteNoncentralFullKernel q n N x lambda).det := by
 have hc : 0 < noncentralKernelLowestMinor q n x lambda := by
   exact weightedGeneralizedMonomialMinorProduct_pos n (fun i : Fin n => i.val)
     x lambda (fun i => noncentralKernelSeriesWeight q i.val) Fin.val_injective
       hx hl hxp hlp (fun i => seriesWeight_pos q i.val)
 have hb := finiteNoncentralFullKernel_det_lower_bound q n N hN x lambda hx hl hxp hlp
 have hp : 0 < (n.factorial : ℝ) := by positivity
 exact (mul_pos_iff_of_pos_left hp).mp (lt_of_lt_of_le hc hb)

end
end JinWishart
#print axioms JinWishart.finiteNoncentralFullKernel_det_lower_bound
#print axioms JinWishart.finiteNoncentralFullKernel_det_pos
