# General Bartlett volume and actual Wishart absolute continuity

Seven Codex modules, 28 printed declarations, locked Lean standard axioms only:

| Module | Count | Checked contribution |
|---|---:|---|
| CentralBartlettFiberVolume | 9 | Fixed-positive-pivot r^-n volume, measurable inverse, density transport, real-coordinate alignment |
| CentralBartlettVolumeTransport | 2 | Tonelli combines positive r to a general r^n-weighted mixed-coordinate volume map |
| GaussianComplexColumnDensity | 1 | Actual arbitrary-dimensional CN(0,I_n) density pi^-n exp(-norm^2), including n=0 |
| HermitianBlockCoordinates | 5 | General volume-preserving (n+1)^2 real-coordinate block equivalence, with exact coordinate formula |
| CentralBartlettCoordinateJacobian | 3 | Chart equals real coordinates of the generic Gram reconstruction; canonical weighted volume map |
| CentralWishartAbsoluteContinuity | 5 | Actual canonical Bartlett recursion, positive Gamma domination, and actual central t>=s coordinate domination |
| NoncentralWishartAbsoluteContinuity | 3 | Shifted Gaussian domination; all-shape noncentral Gram dominated by central; t>=s noncentral full-dimensional coordinate domination |

The final two modules prove statements about the actual Gaussian pushforwards,
without a density hypothesis. The central proof inducts on columns with fixed
row surplus. The noncentral proof transports null sets through the explicit
encoded mean translation. It does not extrapolate central Bartlett independence
to nonzero means. The comparison noncentral<<central holds for all shapes;
domination by s^2 real Lebesgue is asserted only when columns<=rows.

The volume theorem is a general weighted measure identity, not an asserted
pointwise Frechet determinant. The coordinate measure is nested Pi Lebesgue,
not Frobenius-normalized volume or restricted 2s^2-dimensional ambient volume.
The zero pivot is excluded before multiplying by r^-n; zero dimension is retained.

## Preflight and reused exact assets

Before proof, inspect the locked Haar scaling, translation, skew_product,
finite Pi split/reshuffle and real-isometry volume theorems. Reuse the explicit
Hermitian coordinate measure, prior real 2n Gaussian density, existing column
orthonormal encoding, and actual full Bartlett Gram recursion. No new radial
integral, repeated full-rank proof, measurable frame selection, candidate-density
hypothesis or library upgrade was introduced. The nonexistent generic Matrix
`volume` instance was avoided by using the explicit named coordinate measure;
only SigmaFinite and translation invariance were needed, rather than a stronger
unnecessary additive-Haar instance.

Exact SymPy controls use the ROW z^H z convention at n=0,1,2,3; seed=0 records
that there is no random sampling. They check fiber Jacobian r^n against the
known triangular scaling control. Earlier full real-matrix small-dimension
Jacobian controls are in WISHART_CHOLESKY_JACOBIAN_CONTROL_20261015.json;
the actual seed20261017 four-shape x200000 trace/logdet control and existing
rank-one noncentral ncx2 trace controls were reused, not regenerated. Numeric
or finite symbolic controls are not proofs of generic measure statements.

## Verification and review

Final leaf logs: fiber-6, transport-3, column-density-2, block-coordinates-1,
coordinate-jacobian-2, absolute-continuity-2, noncentral-2. Genuine failed logs
remain, including missing explicit scalar types, insufficient/overstrong measure
instances, function-composition rewriting and namespace/scope errors. No failures
are promoted to accepted evidence. Every accepted public theorem/instance has
printed standard axioms and is scanned for holes/unsafe/custom axioms.

Three real Qoder cross-family requests, exact supplied snapshots and feedback
are retained. **REVIEW_RESOLUTION.md** answers specific misreadings in the second
report using the exact restriction/probability/kernel obligations. This is not
unqualified model approval or completed human review. **[需人工审查]** Measure
transport, Tonelli, coordinate volume, variance and model-to-paper interpretation.

`spec.json` / `audit.json` bind leaf source/compiled/log/direct-import hashes,
controls and real review snapshots. The separate main-entry receipt is a cached
dependency compilation, not a full Lake/mathlib rebuild. The frozen paper/PDF
and submission archives are unchanged.

## Still open

Absolute continuity establishes existence of densities, not their closed forms.
The general central formula K(s,t)*det(W)^(t-s)*exp(-trace W) on the PD cone
still needs the actual density induction, cone identification, trace algebra
and normalization recurrence. Noncentral closed density, general spectral G2,
paper Theorems1-4 and the T3 journal/source constant issue are not closed here.
