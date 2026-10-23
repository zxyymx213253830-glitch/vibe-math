import JinWishartFormalization.NaturalNuttallNormalization
import JinWishartFormalization.Theorem2SingleColumnAnyRows

/-! Remove the assumed nonzero Nuttall denominator in every positive-row,
rank-one noncentral formula. Codex; controls seed2026102249 precede source.
This is formula-side normalization, not the missing general-row actual law.
[需人工审查] Original paper parameter and variance correspondence. -/
namespace JinWishart
noncomputable section

private theorem oneColumnZero (t : ℕ) (ht : 1≤t) (lambda : ℝ) :
    nuttallQ t (t-1) (Real.sqrt (2*lambda)) 0=
      (Real.sqrt (2*lambda) : ℂ)^(t-1) := by
  have h := nuttallQ_succ_self_zero (t-1) (Real.sqrt (2*lambda))
  have ht' : t-1+1=t := Nat.sub_add_cancel ht
  rwa [ht'] at h

private theorem oneColumnZero_ne (t : ℕ) (ht : 1≤t) (lambda : ℝ) (hl : 0<lambda) :
    nuttallQ t (t-1) (Real.sqrt (2*lambda)) 0≠0 := by
  rw [oneColumnZero t ht lambda]
  apply pow_ne_zero
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'

theorem theorem1OneColumnCandidate_eq_explicitNormalizedQ
    (t : ℕ) (ht : 1≤t) (lambda x : ℝ) (hl : 0<lambda) :
    theorem1CdfCandidate 1 t 1 ht (by omega) (fun _ : Fin 1 => lambda) x=
      1-‖theorem1OneColumnNuttallQ t lambda x‖/(Real.sqrt (2*lambda))^(t-1) := by
  rw [theorem1OneColumnCandidate_eq_normalizedNuttallQ t ht lambda x
    (oneColumnZero_ne t ht lambda hl),oneColumnZero t ht lambda,
    norm_pow,Complex.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem theorem2OneColumnCandidate_eq_explicitNormalizedQ
    (t : ℕ) (ht : 1≤t) (lambda x : ℝ) (hl : 0<lambda) :
    theorem2CdfCandidate 1 t 1 ht (by omega) (fun _ : Fin 1 => lambda) x=
      ‖(Real.sqrt (2*lambda) : ℂ)^(t-1)-theorem1OneColumnNuttallQ t lambda x‖/
        (Real.sqrt (2*lambda))^(t-1) := by
  rw [theorem2OneColumnCandidate_eq_normalizedNuttallQIncrement t ht lambda x
    (oneColumnZero_ne t ht lambda hl),oneColumnZero t ht lambda,
    norm_pow,Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  rfl

end
end JinWishart
#print axioms JinWishart.theorem1OneColumnCandidate_eq_explicitNormalizedQ
#print axioms JinWishart.theorem2OneColumnCandidate_eq_explicitNormalizedQ
