# Candidate tail probability and paper Psi ratio

For natural p, L, q, strictly increasing positive noncentral parameters, and x >= 0, the checked candidate measure's all-coordinates-greater-than-x probability equals the norm of the original formula-side Psi determinant at x divided by its norm at zero. This includes empty dimensions. This is a statement about the candidate measure, not an identification with the actual Wishart spectrum. Seed 2026103010 supplied 54 numerical checks and 24 negative controls before the source; these are not proofs.

The exact locked source received a tool-disabled Qoder Qwen3.8-Max P4 review. Its warnings were checked against the actual source and dependencies:

* The denominator positivity theorem `mixedEnsemble_momentMatrix_det_pos` is already proved with exactly `StrictMono lambda` and strictly positive entries. Its determinant is the same full moment matrix used by division; no positive-definite matrix premise is asserted.
* `paperPsi_tail_matrix_transport` explicitly expresses the transported complex matrix as `Complex.ofRealHom.mapMatrix` of a real matrix. `Complex.ofRealHom.map_det` supplies the determinant coercion. Thus the real determinant is typed by construction; there is no circular use of determinant positivity.
* `mixedEnsemble_pair_moment` proves L1 on `Ioi 0` for each product under nonnegative parameters; restrictions to `Ioi x` inherit integrability. Lean Bochner integrals are totalized, not undefined or infinite real values. `mixedCandidateEnsemble_allIn` explicitly applies the pair-moment L1 theorem and the positive normalizer.
* For x >= 0, `Ioi x` is contained in `Ioi 0`, matching the restriction rewrite. The source is kernel checked against that API.
* `mixedCandidateEnsemble_probability` proves the candidate measure is a probability measure under the stated hypotheses, so event measures are finite. `mixedCandidateEnsemble_all_gt` establishes the relevant real-valued event formula under the same assumptions.

P4 is not human review or independent compilation. [需人工审查] Improper integrals, Fubini, index conventions, and correspondence with the paper's actual random-matrix model remain. Frozen publication artifacts unchanged; full Lake build and independent Linux kernel NOT_RUN.
