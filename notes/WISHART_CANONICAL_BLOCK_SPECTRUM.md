# Canonical diagonal-block spectrum and shear: exact deterministic step

2026-10-22. Eight new public declarations in two modules, written by Codex.
This closes the diagonal-block spectral identity and the algebraic shear step;
the general singular smallest-positive inverse-moment theorem remains OPEN.

For arbitrary complex A:a-by-b and N:c-by-d, including zero dimensions and
singular or zero blocks, E=diag(A,N) satisfies

    E^H E = diag(A^H A,N^H N),
    charpoly(E^H E) = charpoly(A^H A) charpoly(N^H N),
    roots(E^H E) = roots(A^H A) + roots(N^H N) as multisets.

Thus real eigenvalue membership splits between the two blocks, including zero
roots with their actual multiplicities. The public minimum theorem supplies
positive minimum witnesses for E, A and N explicitly, then proves
lambdaPlus(E)=min(lambdaPlus(A),lambdaPlus(N)). It does not assert those
witnesses exist when a block has rank zero. In particular, an ordinary zero
minimum cannot be substituted for a smallest strictly positive value. The
membership/multiset statements still apply to empty and rank-zero blocks.

For square N:c-by-c, H,K:c-by-b and the explicit solve condition N*K=H,

    D=[[A,0],[H,N]], Sminus=[[I,0],[-K,I]], Splus=[[I,0],[K,I]],
    D*Sminus=E, E*Splus=D, Sminus*Splus=Splus*Sminus=I.

There is no hidden inverse operation in these theorems. N invertibility is not
needed if the solve condition is supplied. Taking K=N^-1 H later requires an
actual inverse hypothesis. No shear norm bound, singular-value inequality,
Gaussian normal form, law, independence, or inverse-moment conclusion is
claimed by this bundle. Matrices use Sum indices; the next quantitative bridge
must explicitly transport them to the existing Fin-index comparison APIs.

## Controls and kernel evidence

`experiments/canonical_block_spectrum_control.py`, seed2026102217: 162 shapes /
650 checks, exact normalized complex-rational Gram and characteristic
polynomial identities, numerical positive-spectrum and minimum comparisons,
zero dimensions, repeated diagonal reference and a negative control excluding
zero from the positive minimum. Controls are not proofs. V1 failed because
SymPy tried to sort unsimplified complex products inside its charpoly routine;
its source/failure record is retained. V2 expands each Gram entry before the
same exact comparison; no tolerance or mathematical statement was weakened.
The previously archived singular_block_shear_control.py supplies 20 cases /
81 controls of the same shear/inverse identities, rank and numerical norm
comparisons; those controls still do not prove the general norm estimate.

Both initial leaf checks exited0 with only propext/Classical.choice/Quot.sound.
Final immutable leaf checks and eight independent literal expected-type
comparisons also passed. The sources are CanonicalBlockSpectrum.lean and
CanonicalBlockShear.lean. Facade/audit acceptance is bound by the release JSON,
not inferred from the initial checks alone.

The first audit correctly refused a manifest count of six for the five public
Spectrum exports: the generic target parser had also named the private helper
realRoot as a public target. No proof or type check failed and no such target
was accepted. canonical-export-repair.json and the retained-manifest folder
preserve nine old nodes/locks/acceptance pointers/specification bytes. The v2
manifest retires those live nodes and locks exactly eight public exports. It
reuses the unchanged successful final leaf/type receipts, source and P4 hashes;
there was no source change or repeated Lean run for this metadata repair. The
auditor and standard-axiom requirements were unchanged. The repaired audit
reports PASS688; facade77 real exit0, its inherited nonblocking ring suggestion
has the same log hash as earlier successful facades. The manifest builder now
requires public theorem names to match the explicit axiom-print list before
creating any node, preventing this private-name mismatch in future bundles.

## Different-model P4 and resolution

Real Qoder Qwen3.8-Max P4, full final source, tools disabled: 2026-10-22
08:07:36--08:08:06UTC, real exit0. Raw response, prompt, receipt and snapshot
hashes are archived as p4-canonical-block-final.* / canonical-block-final-*.
The reviewer labels several concerns “actual gap” and then explicitly retracts
them after reading the types: real-to-complex injection, square Gram factors,
and transporting strict positivity through a local/global eigenvalue equality.
Those self-retractions are retained; they are not undisclosed failures.
Its remaining cardinality-dependency observation is not a missing hypothesis:
the left eigenvalues are indexed by Fin(card(Fin b + Fin d)), and each block
by its own Fin(card). No index identification is used to split the roots;
the already imported Hermitian root-multiset theorem and Multiset.mem_add
perform that step. The exact expected types and final kernel checks agree.
The shear identities received no mathematical objection. This is scoped model
review, not blanket approval, human review or an independent compilation.

## P1 normal-form route assessment (not proof)

A separate real bounded Qoder P1 ran 07:59:04--07:59:44UTC, exit0; it was route
planning only. Its kernel/range route is useful after corrections. The proposed
extra intersection M(ker B) with range(B^H) is ill-typed in general: these live
in different ambient spaces, C^m and C^s. No such transversality hypothesis is
accepted. A row unitary is chosen from M(ker B) and its orthogonal complement.
Pulling an ONB of range B back through B restricted to ker(B)^perp already
gives preimages whose images are orthonormal; applying an additional ordinary
Gram-Schmidt to those preimages need not preserve BT=[U,0], so that extra step
is rejected. Whitening the stacked Gram by itself does not normalize B to U.
There is no obstruction to independent a-by-b and c-by-b Gaussian row blocks
when a<b or m<s. Fixed complex isometries/coisometries, with the properCN1
normalization, still need an explicit law and independence proof.

[需人工审查] Later measure/Fubini/AE/inverse-moment/model transport and complex
variance conventions remain required. This deterministic bundle adds no new
measure interchange. Frozen manuscript/PDF/upload/code archives are unchanged;
full Lake/mathlib build and independent Linux kernel remain NOT_RUN.
