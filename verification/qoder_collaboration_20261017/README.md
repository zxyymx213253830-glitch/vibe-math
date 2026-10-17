# Qoder collaboration, 2026-10-17

User completed official login. `--list-models` succeeded and included Qwen3.8-Max;
the real minimal request returned `OK`. Successful request metadata reports
`qmodel_38max`. This identifies the client-reported backend, not independently
verified model weights. No credentials or authorization URLs are archived here.

## Collaboration and ownership

- Qoder/Qwen3.8-Max: bounded P1 route comparison and issues-only P4 feedback,
  without tools, file edits or independent compilation.
- Codex: all seven proof bodies in `GaussianGramDimensions.lean`, integration,
  exact symbolic controls and kernel/provenance audit. No Qoder-authored or local
  DS-authored proof body is claimed.
- The earlier 150-second combined route/code request timed out with no response.
  It was stopped, not retried unchanged. A short route-only request with thinking
  disabled then returned successfully. All real requests/results are retained.

We selected the left-inverse -> injectivity -> complex rank -> restriction of
scalars -> real orthogonal dimension route. Qoder's dismissal of SVD as only
numeric and its assertion that positive-definiteness/invertibility needs
continuity were not accepted: those finite-dimensional results can be formal.
They simply require more assets than this route. `n <= m` follows from Gram
nonsingularity; it is not a missing hypothesis.

## Exact result and scope

Under `IsUnit (Aᴴ*A).det`, arbitrary finite complex m-by-n A has a left-invertible
column map, complex column rank n, real column rank 2n and real orthogonal
dimension 2(m-n). These algebraic results cover n=0 and n=m. The inherited
probability interface requires 0<n<m for positive Gamma shapes. For any SFinite
preceding-matrix measure mu with a.e. nonsingular Gram, the joint law of the
matrix and split fresh-Gaussian energies is
`mu.prod (Gamma(n, rate=1).prod Gamma(m-n, rate=1))`.

This discharges the former two abstract rank premises, using the explicit
measurable projector from the previous milestone. It still **assumes** a.e.
nonsingularity under mu. Actual Gaussian a.e. full column rank, the eventual
CN(0,1) model identification, general Cholesky Jacobian and actual Wishart
matrix density/G2 remain open. No target density is assumed.

## Verification and failures

Five exact symbolic controls (seed20261017), including n=0 and n=m, use exact
realification, nullspace dimensions and a left inverse. A repeated-column
singular example confirms why nonsingularity matters. These finite controls
are not proofs of generic ranks or null-set probability. The first control
implementation used structural SymPy equality, which rejected an unsimplified
zero expression; entrywise exact simplification corrected the control, without
changing the seed or target.

`rank-assets.txt` verifies the locked names and left inverse. Three failed leaf
checks are preserved: the first two simp-only attempts failed to transport
finrank across the conditional submodule; the third included an extra branch
after split_ifs had closed it. These failed logs contain Lean-generated sorryAx
and are **not accepted evidence**. The final `gram-dimensions-4.txt` has seven
printed declarations using only propext/Classical.choice/Quot.sound and exit0.
The final source has no proof placeholders, extra axioms or native_decide.

All checks used the collaborative gate wrapper, serially. Cached imports are
bound by hash; neither the facade nor a complete Lake build was checked here.
The paper and frozen submission archives are unchanged.

## Review reliability and snapshots

The first P4 snapshot and the follow-up labeled p4-final were earlier **failing**
sources. Both real reviews missed elaboration failures and gave excessive
confidence. Their raw responses and exact source snapshots are retained; they
must not be cited as validation of those sources. The p4-final label reflects
the request name, not an accepted final artifact.

`p4-checked` is the only review request bound to the final kernel-checked source.
It includes the real final log and explicitly corrects the earlier unsupported
claims. It is still a limited model review, not independent compilation or
human review. [需人工审查] Real/complex variance, skew-product/measurability and
eventual model correspondence remain flagged. `audit.json` binds final sources,
compiled leaf, imports, logs, controls, prompts and real review responses.
Scoped Git attributes preserve the exact bytes of these new sources and records,
including original Windows review snapshots; they do not change existing files.

CLI usage reports credits in the raw results. A reported zero dollar field does
not mean the requests were free; timeout billing is unknown. No recurring task,
second research runner, toolchain upgrade, credential changes or remote push.

Reproduce: run `experiments/gram_real_dimension_control.py`, then the documented
collaborative_check wrapper on GaussianGramDimensions with a fresh bounded gate,
then `audit.py`. Reproducing model calls is optional and may consume account credits.
