import JinWishartFormalization.GaussianBartlettBlockLaw

/-!
# The actual central Wishart law as a recursive Bartlett block pushforward

Codex proofs. Coefficients z are a ROW: the lower block is B + zᴴ z.
The reconstruction is total, including a zero first column. Its actual joint
input law is already proved, rather than assumed from a candidate density.
[需人工审查] Measurable pushforward, complex variance, and model interpretation.
This is not yet a real-coordinate Jacobian or a matrix/spectral density.
-/

open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def centralBartlettGram {n : ℕ} (r : ℝ) (z : EuclideanSpace ℂ (Fin n))
    (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => Fin.cases
    (Fin.cases (r : ℂ) (fun k => (Real.sqrt r : ℂ) * z k) j)
    (fun k => Fin.cases (star (z k) * (Real.sqrt r : ℂ))
      (fun l => B k l + star (z k) * z l) j) i

theorem continuous_centralBartlettGram (n : ℕ) :
    Continuous (fun p : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℂ) =>
      centralBartlettGram p.1 p.2.1 p.2.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [centralBartlettGram, Fin.cases_zero, Fin.cases_succ] <;> fun_prop

theorem complexGram_apply_inner {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (j k : Fin n) :
    complexGram A j k = inner ℂ (complexMatrixColumn A j) (complexMatrixColumn A k) := by
  simp only [complexGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    complexMatrixColumn, PiLp.inner_apply, RCLike.inner_apply,
    RCLike.star_def, mul_comm]

theorem normalizedColumnCoefficients_mul {m n : ℕ}
    (u : EuclideanSpace ℂ (Fin (m + 1))) (V : Matrix (Fin (m + 1)) (Fin n) ℂ)
    (j : Fin n) :
    (‖u‖ : ℂ) * normalizedColumnCoefficients u V j =
      inner ℂ u (complexMatrixColumn V j) := by
  by_cases hu : u = 0
  · simp [hu, normalizedColumnCoefficients]
  · have hn : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hu
    change (‖u‖ : ℂ) * (inner ℂ u (complexMatrixColumn V j) / (‖u‖ : ℂ)) = _
    field_simp

/-- Pointwise reconstruction, even at a zero pivot (division is totalized). -/
theorem centralBartlettGram_reconstruct {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ) :
    centralBartlettGram (centralBartlettCoordinates A).1
      (centralBartlettCoordinates A).2.1 (centralBartlettCoordinates A).2.2 = complexGram A := by
  let u := complexMatrixColumn A 0
  let V : Matrix (Fin (m + 1)) (Fin n) ℂ := fun i j => A i j.succ
  change centralBartlettGram (‖u‖ ^ 2) (normalizedColumnCoefficients u V)
    (projectedResidualGram u V) = complexGram A
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · change (‖u‖ ^ 2 : ℝ) = complexGram A 0 0
    rw [complexGram_apply_inner]
    rw [Complex.ofReal_pow]
    exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u).symm
  · change (Real.sqrt (‖u‖ ^ 2) : ℂ) * normalizedColumnCoefficients u V j = _
    rw [Real.sqrt_sq (norm_nonneg u), complexGram_apply_inner]
    exact normalizedColumnCoefficients_mul u V j
  · change star (normalizedColumnCoefficients u V i) * (Real.sqrt (‖u‖ ^ 2) : ℂ) = _
    rw [Real.sqrt_sq (norm_nonneg u), complexGram_apply_inner]
    change star (normalizedColumnCoefficients u V i) * (‖u‖ : ℂ) =
      inner ℂ (complexMatrixColumn V i) u
    have h := congrArg star (normalizedColumnCoefficients_mul u V i)
    simpa only [star_mul, Complex.star_def, Complex.conj_ofReal, mul_comm,
      inner_conj_symm] using h
  · change complexGram V i j - star (normalizedColumnCoefficients u V i) *
      normalizedColumnCoefficients u V j + star (normalizedColumnCoefficients u V i) *
      normalizedColumnCoefficients u V j = complexGram V i j
    exact sub_add_cancel _ _

/-- Full actual central Gram distribution, with a lower-dimensional actual
Wishart factor. No positive-definite or full-rank premise is needed. -/
theorem complexWishart_centralBartlett_recursion (m n : ℕ) :
    complexWishart (m := m + 1) (n := n + 1) =
      ((gammaMeasure ((m + 1 : ℕ) : ℝ) 1).prod
        ((standardComplexColumnLaw n).prod (complexWishart (m := m) (n := n)))).map
          (fun p => centralBartlettGram p.1 p.2.1 p.2.2) := by
  have hC : Measurable (centralBartlettCoordinates (m := m) (n := n)) := by
    exact ((measurable_fst.norm.pow_const 2).prodMk
      (measurable_centralBartlettFiber m n)).comp (measurable_matrixColumnSplit (m + 1) n)
  rw [← actualCentralBartlett_block_law m n,
    Measure.map_map (continuous_centralBartlettGram n).measurable hC]
  have hfun : (fun p => centralBartlettGram p.1 p.2.1 p.2.2) ∘
      centralBartlettCoordinates (m := m) (n := n) = complexGram := by
    funext A
    exact centralBartlettGram_reconstruct A
  rw [hfun, complexGaussianMatrixLaw_map_gram]

end
end JinWishart

#print axioms JinWishart.continuous_centralBartlettGram
#print axioms JinWishart.complexGram_apply_inner
#print axioms JinWishart.normalizedColumnCoefficients_mul
#print axioms JinWishart.centralBartlettGram_reconstruct
#print axioms JinWishart.complexWishart_centralBartlett_recursion
