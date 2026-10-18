"""Actual rectangular CN samples versus the one-extra-row minimum polynomial.

Fixed seeds, known trace Gamma and square Exp controls. Numerical evidence is
not proof. Also checks determinant expansion and determinant moments needed by
the proposed cone-polynomial proof.
"""
from datetime import datetime, timezone
import hashlib
import itertools
import json
import math
from pathlib import Path
import numpy as np

SEED = 2026101802
N = 200_000
BATCH = 5000
rng = np.random.default_rng(SEED)
records = []
for n in (1, 2, 3, 4):
    t = n+1
    mins, traces, dets = [], [], []
    for start in range(0, N, BATCH):
        X = (rng.standard_normal((BATCH,t,n))+1j*rng.standard_normal((BATCH,t,n)))/np.sqrt(2)
        W = X.conj().transpose(0,2,1)@X
        mins.append(np.linalg.eigvalsh(W)[:,0])
        traces.append(np.trace(W,axis1=1,axis2=2).real)
        dets.append(np.linalg.det(W).real)
    lam,tr,det = map(np.concatenate,(mins,traces,dets))
    trace_se = (tr.mean()-t*n)/np.sqrt(t*n/N)
    det_mean = math.factorial(t)/math.factorial(t-n)
    det_second = np.prod([k*(k+1) for k in range(t-n+1,t+1)])
    det_se = (det.mean()-det_mean)/np.sqrt((det_second-det_mean**2)/N)
    assert abs(trace_se)<6 and abs(det_se)<6
    tails=[]
    for y in (0.25,0.75,1.5,3.0,5.0):
        x=y/n
        expected=math.exp(-n*x)*sum(math.comb(n,l)*x**l/math.factorial(l) for l in range(n+1))
        empirical=float((lam>x).mean())
        se=(empirical-expected)/math.sqrt(expected*(1-expected)/N)
        assert abs(se)<6
        tails.append(dict(x=x,formula_tail=expected,empirical_tail=empirical,standard_errors=se))
    # Pointwise polynomial determinant expansion on the actual final sample batch.
    errors=[]
    for x in (0.1,0.8,2.0):
        lhs=np.linalg.det(W+x*np.eye(n)).real
        rhs=np.zeros(BATCH)
        for k in range(n+1):
            for S in itertools.combinations(range(n),k):
                rhs += x**(n-k)*(np.linalg.det(W[:,S,:][:,:,S]).real if k else 1.)
        error=float(np.max(np.abs(lhs-rhs)/(1+np.abs(lhs))))
        assert error<1e-10
        errors.append(dict(x=x,max_relative_error=error))
    # Independent known square Exp(n) control on the first n rows.
    V=X[:,:n,:].conj().transpose(0,2,1)@X[:,:n,:]
    square_mean=np.linalg.eigvalsh(V)[:,0].mean()
    square_se=(square_mean-1/n)/(1/n/np.sqrt(BATCH))
    assert abs(square_se)<6
    records.append(dict(rows=t,columns=n,samples=N,trace_Gamma_standard_errors=trace_se,
        determinant_mean_standard_errors=float(det_se),square_Exp_control_standard_errors=float(square_se),
        tails=tails,determinant_polynomial_controls=errors))
report=dict(seed=SEED,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    collected_utc=datetime.now(timezone.utc).isoformat(),records=records,
    status='PASS actual samples, trace Gamma/square Exp controls and determinant polynomial',
    interpretation='Numerical control only; one-extra-row minimum polynomial still requires proof')
out=Path(__file__).resolve().parents[1]/'verification/rectangular_minimum/control.json'
out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report['status'])
