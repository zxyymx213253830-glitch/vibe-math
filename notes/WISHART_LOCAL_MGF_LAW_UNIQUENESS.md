# Local MGF law uniqueness

Codex proof, generic bridge only. Finite measures mu/nu, AE measurable real
X/Y, zero in both interiors of integrableExpSet, and equality of real MGFs
on a neighborhood of zero imply mu.map X = nu.map Y. No probability or
Gaussian hypothesis is hidden; no all-complex-plane MGF equality is assumed.

Seed 2026102251: 90 controls ran before source. They calibrate the intended
Gaussian/kernel application and a finite-support matching-moments negative
control, and are not a proof of analytic uniqueness.

Proof intersects the two convex open real integrability intervals and takes
their inverse image under the REAL-linear real-part map. This is a convex,
hence preconnected, complex strip containing zero and the entire imaginary
axis. The analytic identity theorem propagates the real-axis agreement to
the common strip. Purely imaginary evaluations give characteristic functions;
finite-measure characteristic-function uniqueness then identifies pushforwards.

First gate v1 failed only because the real zero cast was not syntactically
visible to tendsto_ofReal_iff. Its exact source and failure log are retained,
not accepted. v2 explicitly changes the target zero cast and exits 0 with
only propext, Classical.choice, Quot.sound. Final source and literal target
checks also exit 0. Two haveI style suggestions are harmless and unmodified.

## Bounded real Qoder P4 adjudication

Qwen3.8-Max reviewed the full final source, tools disabled, exit 0.
The raw response is preserved. It first labels punctured frequent agreement
insufficient, then retracts that claim. Exact pinned theorem
AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq takes precisely
frequent equality in nhdsWithin of the complement of the center singleton,
and separately center membership; these are hfreq and 0-in-U. Agreement on
a complex open set is not required. The lifted sequence avoids zero and
converges to zero, so its agreement points have the required accumulation.

The linear_preimage query is resolved by the checked term: it is applied
to a CONVEX intersection, not to arbitrary preconnected sets. General
preconnected inverse images would not suffice. The raw response's claim
about an arbitrary preconnected preimage must not be adopted.

The imaginary-axis query also self-retracts. Membership is determined by
Re((t:Complex)*I)=0, not by equality of that complex point to zero. The final
simpa unfolds U and simplifies that real part, then uses h0X/h0Y; it does
not assert t*I=0. No source change was required by the review.

[需人工审查] Analytic continuation, punctured filters, finite pushforwards,
and model applications. P4 is not human review or independent compilation.
General-row actual Gaussian radial law is still OPEN. No publication files changed.
