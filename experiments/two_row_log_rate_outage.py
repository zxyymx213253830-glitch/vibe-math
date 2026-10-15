"""Reproducible controls for the actual weakest-mode log-rate statistic.

This is numerical evidence, not a proof or a formalization of a coding theorem.
The input is an actual 2x2 CN(0,1) matrix, never sampled eigenvalues.
"""
from __future__ import annotations

import json
from pathlib import Path

import numpy as np
from scipy.stats import gamma, kstest

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    seed, count = 20261015, 200_000
    rng = np.random.default_rng(seed)
    h = (rng.normal(size=(count, 2, 2)) +
         1j * rng.normal(size=(count, 2, 2))) / np.sqrt(2.0)
    gram = np.swapaxes(h.conj(), 1, 2) @ h
    eig = np.linalg.eigvalsh(gram)
    minimum, trace = eig[:, 0], eig.sum(axis=1)
    # Independent numerical eigensolver versus the Hermitian quadratic formula.
    a, d = gram[:, 0, 0].real, gram[:, 1, 1].real
    discriminant = np.sqrt((a-d)**2 + 4*np.abs(gram[:, 0, 1])**2)
    error = float(np.max(np.abs(minimum - (a+d-discriminant)/2)))
    controls = {
        "trace_Gamma_shape4_rate1_KS": float(kstest(trace, gamma(a=4).cdf).statistic),
        "minimum_Exp_rate2_KS": float(kstest(minimum, lambda x: -np.expm1(-2*x)).statistic),
        "eigenvalue_formula_max_error": error,
        "trace_mean": float(trace.mean()),
    }
    assert error < 1e-11
    assert controls["trace_Gamma_shape4_rate1_KS"] < 0.01
    assert controls["minimum_Exp_rate2_KS"] < 0.01
    assert abs(trace.mean()-4) < 8*np.sqrt(4/count)
    rows = []
    for amplitude, rho in [(0.5, 0.3), (1.0, 1.0), (2.0, 3.0)]:
        scaled = amplitude**2 * minimum
        rate = np.log1p(rho * scaled)  # natural logarithm, nats per mode
        for target in [-0.2, 0.0, 0.2, 0.7, 1.5]:
            threshold = np.expm1(target)/rho
            event = rate <= target
            assert np.array_equal(event, scaled <= threshold)
            predicted = float(-np.expm1(-2*threshold/amplitude**2)) if target >= 0 else 0.0
            observed = float(event.mean())
            tolerance = 8*np.sqrt(predicted*(1-predicted)/count) + 8/count
            assert abs(observed-predicted) <= tolerance
            rows.append({"amplitude": amplitude, "variance": amplitude**2,
                         "rho": rho, "target_nats": target,
                         "observed": observed, "formula": predicted,
                         "eight_se_plus_eight_over_n": float(tolerance)})
    result = {"seed": seed, "samples": count, "status": "PASS",
              "model": "actual independent CN(0,1) 2x2 entries; H*H",
              "statistic": "log(1+rho*lambda_min((aH)*aH)); per-mode, not total MIMO capacity",
              "evidence_kind": "numerical controls, not proof", "controls": controls, "rows": rows}
    output = ROOT / "verification/WISHART_LOG_RATE_OUTAGE.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS: actual Gaussian controls and 15 log-rate outage cases; seed=20261015; n=200000")


if __name__ == "__main__":
    main()
