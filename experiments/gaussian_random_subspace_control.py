"""Random Gaussian subspace energy controls; numerical evidence, never proof.

The projector depends on independent preceding complex Gaussian columns.
Half-real squared norms equal complex CN(0,1) energy. A deliberately dependent
projector is also checked, to guard against dropping the independence premise.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import math

import numpy as np
from scipy.stats import gamma


def main():
    seed, count = 20261016, 200_000
    rng = np.random.default_rng(seed)
    records = []
    for dimension, rank in [(3, 1), (5, 2)]:
        previous = (rng.normal(size=(count, dimension, rank)) +
                    1j * rng.normal(size=(count, dimension, rank))) / math.sqrt(2)
        fresh = (rng.normal(size=(count, dimension)) +
                 1j * rng.normal(size=(count, dimension))) / math.sqrt(2)
        basis, _ = np.linalg.qr(previous, mode='reduced')
        coefficient = np.einsum('nmk,nm->nk', basis.conj(), fresh)
        projected = np.sum(np.abs(coefficient)**2, axis=1)
        residual = np.sum(np.abs(fresh)**2, axis=1) - projected
        previous_energy = np.sum(np.abs(previous)**2, axis=(1, 2))
        checks = []

        def check(label, event, exact, selected=None):
            event = event if selected is None else event[selected]
            observed = float(np.mean(event))
            se = math.sqrt(exact * (1 - exact) / len(event))
            assert abs(observed - exact) < 6 * se + 2 / len(event), label
            checks.append(dict(label=label, N=len(event), empirical=observed,
                               exact=float(exact), deviation_SE=abs(observed-exact)/se))

        # An independent closed-form variance control for the actual fresh sample.
        check('total_energy_Gamma_dimension', projected + residual <= dimension,
              gamma.cdf(dimension, dimension))
        for x, y in [(0.5, 1.0), (1.0, 2.0), (2.0, 3.0)]:
            check(f'joint_CDF_{x}_{y}', (projected <= x) & (residual <= y),
                  gamma.cdf(x, rank) * gamma.cdf(y, dimension-rank))
        # The same joint law in parameter-dependent norm and direction bins.
        selected_bins = [previous_energy <= np.median(previous_energy),
                         previous_energy > np.median(previous_energy),
                         previous[:, 0, 0].real <= 0,
                         previous[:, 0, 0].real > 0]
        for j, selected in enumerate(selected_bins):
            check(f'parameter_bin_{j}', (projected <= rank) &
                  (residual <= dimension-rank),
                  gamma.cdf(rank, rank) * gamma.cdf(dimension-rank, dimension-rank),
                  selected)
        # If the subspace is chosen from fresh itself, the residual vanishes.
        dependent_residual = np.sum(np.abs(fresh)**2, axis=1) - np.abs(
            np.sum(fresh.conj()*fresh, axis=1) /
            np.linalg.norm(fresh, axis=1))**2
        assert np.max(np.abs(dependent_residual)) < 1e-12
        assert gamma.cdf(0.5, dimension-1) < 0.5
        records.append(dict(dimension=dimension, complex_rank=rank, checks=checks,
                            dependent_projector_residual_max=float(np.max(
                                np.abs(dependent_residual))),
                            negative_control='Dependent projector violates Gamma residual law'))
    output = Path(__file__).resolve().parents[1] / 'verification/WISHART_RANDOM_SUBSPACE_CONTROL_20261016.json'
    output.write_text(json.dumps(dict(utc=datetime.now(timezone.utc).isoformat(),
        seed=seed, N_per_case=count, source_sha256=hashlib.sha256(
            Path(__file__).read_bytes()).hexdigest(), records=records,
        status='PASS numerical controls only; not proof'), indent=2), encoding='utf-8')
    print('PASS random-subspace Gamma controls and dependent-projector negative control.')


if __name__ == '__main__':
    main()
