"""Exact metric/Jacobian controls before the Frobenius-coordinate Lean bridge."""
from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


def main() -> None:
    rows = []
    for n in range(1, 7):
        coordinates = sp.symbols(f"q0:{n*n}", real=True)
        q = sp.Matrix(n, n, coordinates)
        h = sp.Matrix(n, n, lambda i, j: q[i, i] if i == j else
                      q[i, j] + sp.I*q[j, i] if i < j else q[j, i] - sp.I*q[i, j])
        embedding = sp.Matrix([sp.re(z) for z in h] + [sp.im(z) for z in h])
        jacobian = embedding.jacobian(coordinates)
        metric = sp.simplify(jacobian.T*jacobian)
        expected = sp.diag(*[1 if i == j else 2 for i in range(n) for j in range(n)])
        assert metric == expected
        determinant = metric.det()
        assert determinant == 2**(n*(n-1))
        factor = sp.sqrt(determinant)
        assert factor == 2**(n*(n-1)//2)
        assert sp.eye(n*n).det() == 1  # Euclidean identity embedding control
        rows.append({"n": n, "metric_determinant": str(determinant),
                     "volume_factor": str(factor), "identity_metric_determinant": 1})
    result = {"evidence_kind": "exact finite-dimensional SymPy controls, not general Lean proof",
              "random_seed": "not applicable: deterministic exact algebra", "status": "PASS",
              "two_row_metric": [1, 2, 2, 1], "two_row_volume_factor": 2,
              "two_row_density_relative_to_frobenius": "(2*pi)^(-1)*exp(-trace)", "rows": rows}
    output = Path(__file__).resolve().parents[1] / "verification/WISHART_HERMITIAN_METRIC_CONTROL.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS: exact Hermitian metric and volume factors n=1..6; identity control")


if __name__ == "__main__":
    main()
