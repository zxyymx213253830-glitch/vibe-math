"""Register explicit unproved obligations, without fabricating Lean declarations."""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
cards=[
 ('L-rectangular-cauchy-binet',False,[],
  'For complex A q-by-m and B m-by-q, det(AB)=sum over q-subsets I of m det(A[:,I])*det(B[I,:]); includes q=0 and q>m.',
  ['Expand determinant multilinearly in rows or columns; duplicate intermediate indices vanish by alternatingness.','Group injective intermediate-index functions by image subset, keeping permutation signs and empty case.']),
 ('L-gram-minor-coefficient',False,['L-rectangular-cauchy-binet'],
  'Coefficient q of det(I+t X^H X) equals sum of squared absolute values of ALL q-by-q coordinate minors of arbitrary complex rectangular X.',
  ['Use pinned coeff_det_one_add_X_smul_eq_sum_minors for Gram principal minors.','Apply rectangular Cauchy-Binet to X[:,J], then sum J; retain conjugation.']),
 ('L-gram-rank-spectral-coefficient',False,[],
  'For rectangular complex X of rank r, coefficient r of det(I+t X^H X) is the positive product of its strictly positive eigenvalues; coefficient0=1 when rank0.',
  ['Prove polynomial determinant spectral identity from unitary diagonalization.','Use nonnegative spectrum, rank equals number positive eigenvalues, and finite-product coefficient.']),
 ('S17-general-singular-offset',True,['L-gram-minor-coefficient','L-gram-rank-spectral-coefficient','S15-compressed-log','S16-offset-aggregate-log'],
  'For all fixed rectangular complex B p-by-n,M m-by-n, r=min(m,rank stacked[B;M]), prove aggregate positive-spectrum-log L1 and Elogdet(I+rho X^H X)-r log(rho) tends its finite expectation, X=ZB+M, Z proper independent CN1. No uniformity in B,M.',
  ['At a maximal-rank deterministic witness, positivity of coefficient plus sum-of-squares selects one fixed nonzero coordinate minor.','Establish its physical-entry polynomial is nonzero and its evaluation nonzero AE; use accepted fixed-compression log L1.','On AE rank event derive 2log|P|<=S<=trace and |S|<=trace+2|log|P||. Treat rank0 separately.','Apply accepted conditional aggregate offset after supplying actual aggregate L1.'])]
with a.exclusive(a.PROJECT/'coord/operation.lock','codex-next-bridge-card'):
 for ident,target,deps,statement,steps in cards:
    p=a.PROJECT/'dag/nodes'/f'{ident}.json'
    assert not p.exists()
    a.write(p,dict(id=ident,kind='target' if target else 'statement',target=target,
      statement=statement,stmt_deps=[],proof_deps=deps,
      proof=[dict(text=step,uses=deps) for step in steps],
      verification=dict(status='open_not_formalized',evidence='notes/WISHART_NEXT_PSEUDODET_CARD.md')))
 p=a.PROJECT/'dag/nodes/DEFERRED-polynomial-negative-log.json'
 d=a.read(p);d['scope_resolution']='Historical scalar-pilot card: finite independent planar/properCN1 holomorphic polynomial log L1 is now accepted via S11/S13. Arbitrary degenerate Gaussian laws were not specified/proved; retain historical text outside closure.';a.write(p,d)
 rows=a.refresh()
 a.ledger('Next actual singular pseudoDet bridge registered as FOUR OPEN unformalized nodes;285 exact controls and Qoder false inequality alarm preserved. Count remains585.')
 (a.PROJECT/'coord/STATE.md').write_text('# State\n\n585 accepted bound items. Next four nodes OPEN_NOT_FORMALIZED; no Lean declaration or verification implied. Queue records Cauchy-Binet, Gram coefficient identities and unconditional singular offset obligation.\n\nFixed hour ends13:01:41UTC; heartbeat PAUSED; human review REQUIRED.\n',encoding='utf-8')
print(rows)
