# Third-party proof provenance

## Zeta5 Andréief identity

- Upstream: `mo271/Zeta5`, `Apery/Andreief.lean`.
- Pinned commit: `7fe736760f4b96bfdb4334b68e3b3124ecbe10b0`.
- Source: https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Andreief.lean
- License: Apache-2.0; the complete upstream license is preserved in
  `Zeta5-LICENSE.txt`. No root NOTICE file was present at this commit.
- Local file: `../JinWishartFormalization/Andreief.lean`.
- Modifications: narrow `import Mathlib` to six required modules, move namespace
  from `Apery` to `JinWishart.Andreief`, and adapt module documentation to clarify
  that this is not a Wishart density identification. Mathematical proof retained.
- Verified on this project's Lean v4.35.0-rc2 and locked mathlib e18afff.

This proof is reused, not claimed as an original contribution of this project.
It proves the integral identity under explicit pairwise integrability and
SigmaFinite measure assumptions. Sorted eigenvalue chambers and the actual
Gaussian Gram spectral law remain separate proof obligations.
