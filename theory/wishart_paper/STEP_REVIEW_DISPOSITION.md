# Existing Step review: disposition and release changes

Author: **ZHOU XINGYUAN**. Date: 16 October 2026.

The user identified the existing Step5Preview report. This revision uses the
unchanged report `verification/WISHART_P4_REVIEW_RESPONSE_20261016.md`, which
attributes its review to WorkBuddy, Step model family. No new Step invocation
or exact runtime model identifier is asserted by the packaging process.

Before editorial changes, all 96 source hashes and the manuscript hash in the
review manifest were recomputed and matched. The original manifest and TeX
are preserved under `verification/publication_checks/step-review-20261016/`,
with the actual validation result. The separate review artifact retains the
original TeX; the arXiv ancillary code ZIP intentionally excludes TeX sources.
No Lean source changed in this revision.
The updated manuscript has not been independently re-reviewed; its changes
are the editorial dispositions below and author/metadata updates.

| Report item | Disposition |
|---|---|
| I-1 chart domain | Clarified larger auxiliary domain s>0 versus positive Bartlett support s>0,e>0 used for the actual density. |
| I-2 supporting formulas | Explicitly named the supporting (1,2,1) and (1,3,1) candidate-to-actual-CDF specializations, retaining noncentrality and compatibility hypotheses. |
| I-3 general transcription | Preserved the limitation: no equation-by-equation journal comparison or general formula correctness claim. |
| I-4 weak versus strict tail | No proof change needed. Central 2x2 statement remains strict tail, complementary weak CDF. General weak-tail interfaces are not silently substituted. |
| I-5 Frobenius factor | Explicitly labeled the general volume-factor calculation as a textual geometric derivation, not a generic formalized volume theorem. |
| I-6 unreviewed scope | Recorded full/signature-only/unread scope in manuscript section 6.4. No comprehensive semantic acceptance claimed. |

The separate `notes/ARXIV_SUBMISSION_REVIEW_20261016.md` supplied editorial
suggestions. The author line and PDF metadata now use ZHOU XINGYUAN; no
affiliation or email was invented. The working-manuscript date label and two
conspicuous inline draft review callouts were removed. Their substance is
retained in the consolidated human-review obligations. KS statistics are
explicitly associated with their Gamma/Exp controls. Workflow counts and
proof-body provenance remain in the manuscript. The source layout includes
the complete code ZIP as an ancillary file; local packaging is not upload.

The reports are preserved verbatim. Their historical remarks about the empty
author line and a missing independent model report no longer describe the
current snapshot. The existing Step review reported no concrete mathematical
errors in its inspected scope. It did not read every dependency proof and is
not human mathematical review. [需人工审查] remains for measurable skew products,
Fubini specifications, volume/model conventions and source-notation alignment.
The human author still determines release rights/license and takes final
responsibility for the content. General G2 and general Theorems 1-4 remain open.
