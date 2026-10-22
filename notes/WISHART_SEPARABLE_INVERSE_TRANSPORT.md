# Product inverse-moment transport

The public theorem integrable_inverse_rpow_iff_of_separable_comparison proves a generic analytic step needed by canonical singular models. Let mu,nu be probability measures, measurable f(x,y),g(x), a finite real factor K(y)>0, and p>0 with E_nu K^p finite. Assume AE f>0,g>0 and g<=K f, f<=K g on the PRODUCT measure. Then E_(mu product nu) f^(-p) is finite iff E_mu g^(-p) is finite (written as positive powers of reciprocals in Lean).

Sufficiency bounds f inverse-power by g inverse-power times K power and uses the integrable product theorem. Necessity uses Fubini to choose one fixed y for which both the f inverse-power section is integrable and the comparison holds for mu-almost all x. K(y)^p is a finite scalar. This avoids an extra bounded-H event or Holder exponent loss. No uniform bound on K is claimed, no arbitrary dependent joint law is substituted for product measure, and the theorem does not by itself identify the physical singular-model threshold.

Controls: seed2026102233,19 cases/42 closed power-tail controls. Independent examples have exact factor kappa/(kappa-p), critical truncated logarithmic growth and supercritical power growth. A dependent diagonal countercontrol g=a,K=a^(-1/2),f=sqrt(a),p=3/2 has finite f inverse-moment and K moment but divergent g inverse-moment; it demonstrates that the product-law premise matters. Controls are not a proof of the measure theorem. Final v3 and one literal target type passed the shared serial Lean gate with standard three axioms. Failed v1/v2 namespace diagnostics remain archived and unaccepted.

## Qoder P4 resolution

The real final-source Qwen3.8-Max response explicitly retracts its initial inequality-direction and fixed-section objections after checking the conjunction. The helper uses G<=D F to bound inverse(F)^p by D^p inverse(G)^p. Sufficiency supplies g<=K f; necessity supplies f<=K g. Its final conclusion is no mathematical issues found. The remaining swap question is covered by Measure.measurePreserving_swap on the stated product of probability measures and its quasiMeasurePreserving AE pullback. The selected section exists because nu is a probability measure, hence the AE filter is nontrivial. Scoped P4 is not human review or independent compilation.

[需人工审查] Fubini/AE section use, measurability and final physical-model application. General singular B inverse threshold remains OPEN. Frozen paper/PDF/upload/code archives unchanged; full Lake/mathlib and Linux independent kernel NOT_RUN.
