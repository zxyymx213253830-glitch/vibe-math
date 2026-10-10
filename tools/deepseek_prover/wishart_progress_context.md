# Current Wishart formalization progress, 2026-10-10

You are the user's local DeepSeek-Prover-V2-7B model. Codex has read the
repository progress records and provides this bounded handoff so you can
continue the real research, using the existing Lean 4.35.0-rc2/mathlib cache.

Source records read by the orchestrator:
- notes/JIN_WISHART_RESTORED_HOUR_REPORT_20261010.md
- notes/JIN_WISHART_THEOREM_TRACKER.md
- notes/BARTLETT_DENSITY_REUSE_PREFLIGHT_20261010.md
- JinWishartFormalization/TwoRowRandomDirectionLaw.lean
- JinWishartFormalization/TwoRowGramChart.lean

Verified progress: actual central 2x2 complex Gaussian samples have independent
Bartlett coordinates (S,Z,E) with laws Gamma(2,1), CN(0,1), Exp(1).
The actual Gram law is the pushforward under an explicit Bartlett matrix map.
In four real coordinates p=(S,x,y,E), its Gram chart is
q=(S,sqrt(S)*x,sqrt(S)*y,x^2+y^2+E).
The chart has a proved left inverse on S>0, is injective there, and its actual
Frechet derivative determinant is S. Lebesgue nonnegative change of variables
has been proved on that domain.

Missing: complex scalar density/volume bridge, joint Bartlett real-coordinate
density, support/null-boundary bridges, actual Gram density, and then ordered
spectral Jacobian/angular integration. General paper Theorems 1-4 remain open.
Single-column special cases and formula-side identities do not close this gap.
The T3 transcribed candidate has a proved normalization issue; do not silently
replace it with a repaired candidate or declare the paper theorem proved.

Your current subtask advances the support-domain bridge, by characterizing
the exact image of S>0,E>0 under the existing chart as
q0>0 and q1^2+q2^2<q0*q3. This is deterministic algebra, not a new probability
density assumption. Do not claim an almost-sure support theorem from it alone.
Codex runs fixed-seed numerical/analytic controls before requesting this proof.
These controls are not proofs; Lean must check your unchanged target.
No new axioms, unchecked placeholders, native_decide, or weakened assumptions.
Any subsequent measure-theory/model interpretation needs human review.

Exact existing declarations in namespace JinWishart (already imported):

```lean4
abbrev GramChartSpace := Fin 4 → ℝ
def twoRowGramChart (p : GramChartSpace) : GramChartSpace :=
  ![p 0, Real.sqrt (p 0) * p 1, Real.sqrt (p 0) * p 2, p 1 ^ 2 + p 2 ^ 2 + p 3]
def twoRowGramChartInverse (q : GramChartSpace) : GramChartSpace :=
  ![q 0, q 1 / Real.sqrt (q 0), q 2 / Real.sqrt (q 0),
    q 3 - ((q 1 / Real.sqrt (q 0)) ^ 2 + (q 2 / Real.sqrt (q 0)) ^ 2)]
theorem twoRowGramChart_left_inverse (p : GramChartSpace) (hp : 0 < p 0) :
  twoRowGramChartInverse (twoRowGramChart p) = p
theorem twoRowGramChart_injOn :
  Set.InjOn twoRowGramChart {p : GramChartSpace | 0 < p 0}
```

Available Mathlib tactics: simp, ext, fin_cases, field_simp, ring, nlinarith,
positivity. sqrt lemmas: Real.sq_sqrt (h : 0 ≤ s),
Real.sqrt_pos.2 (h : 0 < s). Use the existing inverse as the preimage witness.
Your brief plan should explain where this lemma fits in the remaining gap;
then return ONLY the requested proof-body tactics in one lean4 fence.
