# Actual joint spectrum: bounded route review

An authorized, tool-disabled Qoder P1 response is retained in `verification/sheaf_wishart/quota-20261022-0949/p1-actual-joint-spectrum-route.response.md`. It is exploratory, not evidence of any theorem or library API. The response correctly distinguishes matrix, unordered-spectrum, and ordered-spectrum measures and notes that scalar trace/minimum/maximum marginals are insufficient for joint-law identification. It also identifies the missing angular/HCIZ or an equivalent Jacobian/conditional-kernel step and the need for human review of measure disintegration, Fubini and limits.

The response contains misleading suggestions and is not adopted as a proof plan without repair:

* The constructed `mixedCandidateEnsemble` is an exchangeable measure on the full product coordinate space, not directly a measure restricted to the ordered Weyl chamber. Sorting/pushforward and multiplicities require their own proof.
* Existing results do not establish a general actual central rectangular joint eigenvalue density in arbitrary dimension. A central formula-side normalization or a central minimum polynomial is not that density.
* Continuously changing the mean from zero to M proves continuity of actual laws, but does not identify a candidate law at the endpoint without a separate identity for the interpolating family; equality at zero and scalar trace agreement do not supply it.
* Appending a column gives a larger bordered Gram matrix; it is not literally the same-dimensional rank-one update `W_k + w*w^H`. Appending a row yields such an update but changes the induction setup and the conditional angular law must still be constructed.
* Repeated noncentral eigenvalues of the deterministic mean matrix do not by themselves imply repeated random sample eigenvalues occur with positive probability. No such assertion is used here.

The next valuable direction is an independently controlled actual-to-candidate link with a genuine multivariate transform or a concrete matrix-to-spectrum Jacobian. A fixed-dimensional noncentral 2-by-2 law may provide a bounded entry point, but its angular integral and singular/repeated mean limits must be derived rather than assumed. No new actual joint-law identification is claimed.
