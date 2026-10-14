# Mathematical directions for Pu et al. NLOS rain-effects paper

Date: 2026-10-14. This is a reading audit and candidate research agenda.

## Verified numerical checks

Run `D:\miniconda3\python.exe experiments/nlos_multilayer_audit.py`.
No randomness is used. Closed-form controls are the zero-thickness boundary
and the lossless air/n=2/air slab with reflectances 0, 0.36, 0 at phases
0, pi/2, pi. Two independent propagation methods agree on these controls.

For normal incidence, four real indices (1,2,3,1), and finite-layer phases
(pi/4,pi/3), interpreting Eq. (18) as recursively appending an interface to
the total prefix gives reflectance 0.3078427696299345. Backward recursion
and characteristic matrices both give 0.5525919315144388.
This is a reproducible discrepancy for that interpretation. It does not
establish what the authors computed or prove their plotted results wrong.
Definitions, propagation reference planes, and source code require review.

A dimensionless three-layer example has zero-film power transmittance 0.75.
For middle index 2, loss/h^2 tends toward -4.07151; for index 2+0.1i,
loss/h tends toward 0.8686. These are local scaling hints, not a proof of
the paper's rain-rate exponents. The sign convention is exp(-i omega t).

## Candidate directions

1. Audit amplitude recursion, branches, energy flux, and units. The symbol
   mu with units Pa*s in the paper denotes dynamic, not kinematic, viscosity.
2. Derive thin-film asymptotics only where |gamma*h| is small and the dry
   baseline is nonzero. Separate leading linear and quadratic corrections.
3. Study structural identifiability before inversion. In h=C*R^(1/3),
   unknown C and R are inseparable from observations depending only on h;
   (C,R)=(1,8) and (2,1) give identical h. This is a simplified-interface
   example, not an impossibility theorem for every measurement design.
4. Candidate transient closure: h_t + (q(h))_x = rainfall_source - evaporation,
   q= rho*g*cos(alpha)*h^3/(3*mu), with suitable boundary/initial data.
   Approximation validity, dry fronts, solution regularity, and any existence
   or convergence arguments: [需人工审查].
5. Turn fluctuation amplitudes into detection probabilities with noise and
   multipath nuisance parameters; state false-alarm rates explicitly.
6. Treat nonuniform wetting and effective-interface averaging with explicit
   coherent/incoherent observation assumptions. No validity proof is given.

## Verified primary references

- Steven J. Byrnes, Multilayer optical calculations:
  https://arxiv.org/abs/1603.02720
- Yadong Ruan, Ali Nadim, Marina Chugunova, Thin liquid film resulting from
  a distributed source on a vertical wall, Phys. Rev. Fluids 5, 064004 (2020):
  https://arxiv.org/abs/1910.10810

Neither reference alone establishes novelty of the proposed extensions.
