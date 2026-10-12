"""Fixed-seed actual CN(0,1) 2x2 Gram minimum-tail preflight.

Scalar Exp(1), trace Gamma(4,1), and NumPy eigensolver are controls.
The exponential minimum-tail comparison is a conjecture check, not a proof.
"""
from __future__ import annotations

import json
from pathlib import Path

import numpy as np


def main() -> None:
    seed, count = 20261012, 200_000
    rng = np.random.default_rng(seed)
    samples = (rng.standard_normal((count, 2, 2)) +
               1j * rng.standard_normal((count, 2, 2))) / np.sqrt(2)
    gram = np.swapaxes(samples.conj(), -1, -2) @ samples
    a, d = gram[:, 0, 0].real, gram[:, 1, 1].real
    off = np.abs(gram[:, 0, 1]) ** 2
    trace = a + d
    minimum = (trace - np.sqrt((a - d) ** 2 + 4 * off)) / 2
    eig_error = float(np.max(np.abs(
        minimum[:4096] - np.linalg.eigvalsh(gram[:4096])[:, 0])))
    assert eig_error < 1e-12, "Eigensolver control failed"
    scalar = np.abs(samples[:, 0, 0]) ** 2
    controls = {
        "scalar_Exp1_mean": [float(scalar.mean()), 1.0],
        "scalar_Exp1_variance": [float(scalar.var()), 1.0],
        "trace_Gamma4_mean": [float(trace.mean()), 4.0],
        "trace_Gamma4_variance": [float(trace.var()), 4.0],
        "numpy_eigenvalue_max_error": eig_error,
    }
    assert abs(scalar.mean() - 1) < 6 / np.sqrt(count)
    assert abs(scalar.var() - 1) < 6 * np.sqrt(8 / count)
    assert abs(trace.mean() - 4) < 12 / np.sqrt(count)
    assert abs(trace.var() - 4) < 6 * np.sqrt(56 / count)
    rows = []
    for x in [0.0, 0.1, 0.25, 0.5, 1.0, 2.0, 3.0]:
        spectral = minimum > x
        shifted_cone = (a > x) & ((a - x) * (d - x) > off)
        assert np.array_equal(spectral, shifted_cone), "Cone/event control failed"
        observed, conjectured = float(spectral.mean()), float(np.exp(-2 * x))
        sigma = float(np.sqrt(conjectured * (1 - conjectured) / count))
        assert abs(observed - conjectured) <= 6 * sigma + 2 / count
        scalar_tail, scalar_exact = float((scalar > x).mean()), float(np.exp(-x))
        assert abs(scalar_tail - scalar_exact) <= 6 * np.sqrt(
            scalar_exact * (1 - scalar_exact) / count) + 2 / count
        rows.append({"threshold": x, "observed_minimum_tail": observed,
                     "conjectured_exp_minus_2x": conjectured,
                     "six_sigma_tolerance": 6 * sigma + 2 / count,
                     "scalar_Exp1_tail_control": [scalar_tail, scalar_exact]})
    report = {"seed": seed, "sample_count": count,
              "model": "actual CN(0,1) 2x2 samples; Gram X*X",
              "status": "CONTROLS_PASS_CONJECTURE_NOT_REFUTED_NOT_A_PROOF",
              "controls": controls, "tail_comparisons": rows}
    target = Path(__file__).resolve().parents[1] / "verification" / \
        "WISHART_TWO_ROW_MINIMUM_TAIL_20261012.json"
    target.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
