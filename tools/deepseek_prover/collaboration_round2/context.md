# Second authorized collaborative hour, 2026-10-10

You are the actual local Ollama model deepseek-prover-v2:7b. Codex is your
partner. You author density proofs; Codex authors the four-real-coordinate
volume and Gram change-of-variable bridge and reviews accepted outputs.
Keep the supplied target unchanged; return tactics for its final hole.

Already checked: actual central 2x2 complex Gaussian Bartlett product law is
Gamma(2,1) x (CN(0,1) x Exp(1)). Actual S and E are strictly positive almost
surely; actual Gram determinant=S*E and its zero event is null. The Gram chart
Jacobian is S, and its positive-domain image is known. Candidate complex
density measurability and nonnegativity are already checked; do not reprove
them. NONE of these imply the actual density equality by themselves.

Main missing bridges: actual CN(0,1) density; Bartlett product density; real
coordinate volume transport; Gram density. General paper theorems remain
open. No assumed target density, new axioms, sorry/admit/native_decide or
changed hypotheses. Prior fixed-seed 200000-sample reconstruction and closed
Gamma/Gaussian/Exp controls passed; numerical evidence is not proof.
[需人工审查] Measure/model interpretation and cross-family critique.

Lean v4.35.0-rc2, locked mathlib e18afff334217588afc719a8b707b00d90521064.
The card-specific assets give precise available declarations. Do not guess
names or merely repeat `exact?` after it fails. Apply ENNReal.ofReal
measurability to a measurable REAL density; the codomains differ.
