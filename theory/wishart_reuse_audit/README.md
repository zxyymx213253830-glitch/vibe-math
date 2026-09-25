# Wishart Lean reuse and compatibility audit

This directory is an isolated audit scaffold. It does not alter `theory/jin_wishart_formalization`, does not vendor the upstream GPL-3.0-only source, and is not part of a committed change. The source archive was inspected in place at `C:\Users\zxy1117\AppData\Local\Temp\wishart_lean_source_audit\unzipped\LogDetBerryEsseen_Full_Lean_v1.1.4`; its ZIP SHA-256 checked locally is `D5172DE1E5B338B140485F816950CA638D9B776B5927147A05CE235B5A26769C`.

## Upstream examined

- Full archive: <https://zenodo.org/records/22739087> (v1.1.4, published 2026-09-13).
- Concise public repository: <https://github.com/HongruZhao/LogDetBerryEsseen>.
- Upstream `lean-toolchain`: `leanprover/lean4:v4.33.0-rc2`.
- Upstream `lakefile.toml` pins Mathlib revision `641fbd329d4ffb62bef83c51f54088469056bd36`.
- Upstream source license: GPL-3.0-only. Do not copy source files into the Jin project without an explicit licensing decision.

The archive was locally extracted and its source import headers checked. The following exact Lean module names correspond to files under `LogdetLean/`:

| Archive file | Candidate Lean import | Reuse potential |
| --- | --- | --- |
| `PaperComplexWishartTransform.lean` | `LogdetLean.PaperComplexWishartTransform` | Paper-facing complex Wishart transform and original-sample bridge; closest direct transform layer. |
| `PaperComplexWishartFormula.lean` | `LogdetLean.PaperComplexWishartFormula` | Complex multivariate-gamma factors and product formula. |
| `PaperComplexWishartKernel.lean` | `LogdetLean.PaperComplexWishartKernel` | Sequential factorization and nested complex Wishart kernel. |
| `PaperComplexWishartFactors.lean` | `LogdetLean.PaperComplexWishartFactors` | Complex-gamma/Mellin and sequential-kernel factors. |
| `WishartComplexTransform.lean` | `LogdetLean.WishartComplexTransform` | Complex diagonal-stage, identity, and correlation transforms. |
| `WishartComplexMGF.lean` | `LogdetLean.WishartComplexMGF` | MGF/characteristic-function and holomorphic-strip layer. |
| `WishartActualComplexBridge.lean` | `LogdetLean.WishartActualComplexBridge` | Bridge from encoded actual complex Wishart model to the complex transform. |
| `PaperWishartHolomorphicLog.lean` | `LogdetLean.PaperWishartHolomorphicLog` | Holomorphic logarithm of the transform and its derivatives. |
| `PaperPartitionedWishart.lean` | `LogdetLean.PaperPartitionedWishart` | Partitioned real Wishart/scatter law and Schur-complement factorization. |
| `PaperKibbleDensity.lean` | `LogdetLean.PaperKibbleDensity` | Kibble density result; related density technology, but not automatically the target noncentral eigenvalue density. |
| `PaperKibbleJointLaw.lean` | `LogdetLean.PaperKibbleJointLaw` | Joint-law layer supporting the Kibble density result. |
| `PaperJointLaguerre.lean` | `LogdetLean.PaperJointLaguerre` | Joint Laguerre identities; potentially useful for determinant expansions/integrals. |
| `PaperLaguerreCoordinates.lean`, `PaperLaguerreGenerating.lean`, `PaperLaguerreGeneratingL2.lean`, `PaperLaguerreL2.lean`, `PaperLaguerreLaplace.lean`, `PaperLaguerreMoments.lean`, `PaperLaguerreRodrigues.lean` | matching `LogdetLean.*` modules | Laguerre basis, generating functions, and integral identities. |

Checked dependency edges: `PaperComplexWishartTransform` imports `PaperComplexWishartKernel`, `PaperComplexWishartFormula`, and `PaperPartitionedWishart`; the kernel imports `PaperComplexWishartFactors`; the formula imports those factors and `PaperDiagonalLog`. `WishartComplexTransform` imports `WishartMellinLaplace` and `WishartPopulationCorrection`; `WishartMellinLaplace` imports `WishartBetaGammaFactors`, `BetaMellin`, and `GammaMellin`. `WishartActualComplexBridge` imports `WishartSequentialKernel` and `WishartComplexTransform`; `WishartComplexMGF` imports that bridge. `PaperKibbleDensity` and `PaperJointLaguerre` both import `PaperKibbleJointLaw`, which imports `PaperLancasterLaplace`, `PaperLaplaceDensityIdentification`, and `RadialLaplaceKernel`.

The source import paths are confirmed, but the upstream modules have not been compiled/imported in the Jin project. The archive contains source only, no `.lake` build artifacts.

## Version compatibility

The Jin project uses Lean `4.35.0-rc2` and Mathlib revision `e18afff334217588afc719a8b707b00d90521064`. The upstream archive uses Lean `4.33.0-rc2` and a different Mathlib revision. Lean's compiled `.olean` artifacts are toolchain/build-context specific, so they must not be assumed import-compatible across these pins. A source port or a separate upstream-pinned Lake project is the safe first test. This audit's `MathlibSmoke.lean` tests only the locally installed Jin toolchain/Mathlib context, not the upstream modules.

## Minimal reuse map for the Jin paper

Likely reuse candidates:

1. Complex Gaussian / Wishart transform calculations and their analytic foundations: `WishartComplexTransform`, `WishartComplexMGF`, `WishartActualComplexBridge`.
2. Kibble density and bivariate/joint Laguerre tools: `PaperKibbleDensity`, `PaperKibbleJointLaw`, `PaperJointLaguerre`, and the `PaperLaguerre*` modules.
3. Matrix partition/Schur machinery: `PaperPartitionedWishart`, with general spectral primitives from `WishartSpectralRotation` / `CorrelationSpectralAlgebra` if their statements fit.

Important gap: this upstream work concerns Gaussian sample-correlation log-determinants and central/diagonal complex Wishart transforms. It does **not** by itself establish the Jin paper's noncentral multi-column Wishart eigenvalue joint density, Vandermonde/eigenvalue Jacobian, smallest/largest-eigenvalue determinant formulas, or final SER/outage claims. Those statements still require a theorem-by-theorem match and additional proof.

## Reproduce local smoke

The local `MathlibSmoke.lean` was checked successfully with the Jin Lean 4.35.0-rc2 executable and existing compiled Mathlib paths (exit code 0). No Lake build was run. `lake env` stalled for 30 seconds in the shared checkout, so the passing smoke used direct Lean with these search paths, from repository root:

```powershell
$lean = Join-Path $env:USERPROFILE '.elan\toolchains\leanprover--lean4---v4.35.0-rc2\bin\lean.exe'
$pkgRoot = Resolve-Path 'theory\jin_wishart_formalization\.lake\packages'
$paths = @((Resolve-Path 'theory\jin_wishart_formalization\.lake\build\lib\lean').Path)
Get-ChildItem $pkgRoot -Directory | ForEach-Object { $p = Join-Path $_.FullName '.lake\build\lib\lean'; if (Test-Path $p) { $paths += (Resolve-Path $p).Path } }
$env:LEAN_PATH = $paths -join ';'
& $lean theory\wishart_reuse_audit\MathlibSmoke.lean
```

Because this invokes only `lake env lean` in the existing local dependency context, it should not rebuild the Jin library. Do not run the command concurrently with another Lake operation on the same cache.

## Next validation step

Next, run the upstream project in a separate checkout under its pinned Lean 4.33.0-rc2 and Mathlib revision. Only Lean 4.35.0-rc2 is installed locally, so the upstream build/import remains unverified. Do not add upstream GPL source as a dependency or copy it into the Jin package before deciding whether the license is acceptable.
