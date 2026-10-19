"""Fixed-seed low-scale logdet curvature controls; numerical evidence, not proof."""
import hashlib
import json
from pathlib import Path
import numpy as np

SEED = 2026101925
SAMPLES = 200_000
rng = np.random.default_rng(SEED)
records = []
for m, n, amplitude in [(1, 1, 0.), (1, 3, 0.), (2, 2, .3), (4, 2, .2), (2, 4, .4)]:
    mean = amplitude * (np.arange(m*n).reshape(m, n) + 1) / (m*n)
    mean = mean + 1j * mean[::-1] / 3
    gram_mean = mean.conj().T @ mean
    fro2 = float(np.vdot(mean, mean).real)
    trace_control = m*n + fro2
    second_control = m*n*(m+n) + 2*(m+n)*fro2 + float(np.trace(gram_mean@gram_mean).real)
    eigs = []
    traces = []
    for _ in range(SAMPLES // 20_000):
        z = (rng.standard_normal((20_000, m, n)) + 1j*rng.standard_normal((20_000, m, n))) / np.sqrt(2)
        x = z + mean
        # Singular values squared avoid artificial negative zeros in wide Gram matrices.
        lam = np.linalg.svd(x, compute_uv=False)**2
        eigs.append(lam)
        traces.append(np.sum(np.abs(x)**2, axis=(1, 2)))
    lam = np.concatenate(eigs)
    trace = np.concatenate(traces)
    second = (lam**2).sum(axis=1)
    trace_se = np.sqrt((m*n + 2*fro2) / SAMPLES)
    second_se = second.std(ddof=1)/np.sqrt(SAMPLES)
    assert abs(trace.mean()-trace_control) < 6*trace_se
    assert abs(second.mean()-second_control) < 6*second_se
    # Scalar/one-row central laws give independent Gamma first/second-moment controls.
    if amplitude == 0 and m == 1:
        assert second_control == n*(n+1)
    values = []
    for rho in [1., .1, .01, .001, .0001]:
        gap = ((rho*lam - np.log1p(rho*lam))/rho**2).sum(axis=1)
        assert gap.min() >= -1e-10
        assert np.all(gap <= second/2 + 1e-7)
        values.append(dict(rho=rho, mean_gap_quotient=float(gap.mean()),
                           sample_half_second=float(second.mean()/2)))
    assert abs(values[-1]['mean_gap_quotient']/(second.mean()/2)-1) < .02
    # A first moment is not the curvature; detect this incorrect candidate.
    assert abs(second_control-trace_control) > 10*second_se
    records.append(dict(m=m, n=n, mean_real=mean.real.tolist(), mean_imag=mean.imag.tolist(),
                        trace_observed=float(trace.mean()), trace_control=trace_control,
                        trace_SE=float(trace_se), second_observed=float(second.mean()),
                        second_control=second_control, second_SE=float(second_se), values=values))
report = dict(seed=SEED, samples_per_shape=SAMPLES,
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              status='PASS actual CN curvature, trace, scalar Gamma and wrong-first-moment controls; NOT proof',
              candidate='EtrW2=mn(m+n)+2(m+n)||M||F2+tr((M^H M)^2); not yet formalized',
              zero_shapes='Exact empty sums give zero, no random draws needed', records=records)
out = Path('verification/central_mixed_moments/logdet-second-order-control.json')
out.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
print(report['status'])
