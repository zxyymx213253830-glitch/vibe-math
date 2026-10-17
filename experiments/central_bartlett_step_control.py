"""Preflight for one general central Bartlett block step; numerical, not proof."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import numpy as np
from scipy.special import digamma, polygamma
from scipy.stats import gamma


def main():
    rng = np.random.default_rng(20261017)
    count = 200_000
    records = []
    for m, n in [(3, 2), (5, 2), (4, 3)]:
        rs, zs, bs, ds, signs = [], [], [], [], []
        for _ in range(count//5000):
            a = (rng.normal(size=(5000, m, n+1)) +
                1j*rng.normal(size=(5000, m, n+1)))/np.sqrt(2)
            u, v = a[:, :, 0], a[:, :, 1:]
            r = np.sum(np.abs(u)**2, axis=1)
            z = np.einsum('bi,bij->bj', u.conj(), v)/np.sqrt(r[:, None])
            b = v.conj().transpose(0, 2, 1)@v-z.conj()[:, :, None]*z[:, None, :]
            eigenvalues = np.linalg.eigvalsh(b)
            assert np.all(r > 0) and np.all(eigenvalues > 0)
            rs.append(r)
            zs.append(np.sum(np.abs(z)**2, axis=1))
            bs.append(np.trace(b, axis1=1, axis2=2).real)
            ds.append(np.linalg.slogdet(b)[1])
            signs.append(u[:, 0].real <= 0)
        r, z, b, d, direction = map(np.concatenate, [rs, zs, bs, ds, signs])
        shapes = np.arange(m-n, m)
        d_mean, d_var = np.sum(digamma(shapes)), np.sum(polygamma(1, shapes))
        d_z = (d.mean()-d_mean)/np.sqrt(d_var/count)
        assert abs(d_z) < 6
        checks = []
        for label, event, expected in [
            ('r_Gamma_m', r<=m, gamma.cdf(m, m)),
            ('z_energy_Gamma_n', z<=n, gamma.cdf(n, n)),
            ('B_trace_Gamma', b<=(m-1)*n, gamma.cdf((m-1)*n, (m-1)*n)),
            ('joint_r_z_B', (r<=m)&(z<=n)&(b<=(m-1)*n),
                gamma.cdf(m, m)*gamma.cdf(n, n)*gamma.cdf((m-1)*n, (m-1)*n))]:
            se = np.sqrt(expected*(1-expected)/count)
            standard_errors = float((event.mean()-expected)/se)
            assert abs(standard_errors) < 6
            checks.append(dict(label=label, deviation_standard_errors=standard_errors))
        expected = gamma.cdf(n, n)*gamma.cdf((m-1)*n, (m-1)*n)
        joint = (z<=n)&(b<=(m-1)*n)
        for label, selected in [('small_r', r<=m), ('large_r', r>m),
                                ('direction_minus', direction), ('direction_plus', ~direction)]:
            se = np.sqrt(expected*(1-expected)/selected.sum())
            standard_errors = float((joint[selected].mean()-expected)/se)
            assert abs(standard_errors) < 6
            checks.append(dict(label=label, N=int(selected.sum()), deviation_standard_errors=standard_errors))
        records.append(dict(rows=m, remaining_columns=n, N=count, checks=checks,
                            residual_logdet_deviation_standard_errors=float(d_z)))
    root = Path(__file__).resolve().parents[1]
    folder = root/'verification/central_bartlett_step'
    folder.mkdir(exist_ok=True)
    (folder/'control.json').write_text(json.dumps(dict(seed=20261017,
        collected_utc=datetime.now(timezone.utc).isoformat(), records=records,
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        control='Gamma r/z/B-trace and lower-row Wishart logdet closed moments, joint/bin controls',
        status='PASS numerical preflight only; full B matrix law remains a proof obligation'),
        indent=2)+'\n', encoding='utf-8')
    print('PASS 3 block-step shapes x200000; Gamma/logdet/joint/direction controls, not proof.')


if __name__ == '__main__':
    main()
