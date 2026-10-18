"""Exact counterexample to the reviewer's proposed row-Gram conjugation swap."""
import hashlib
import json
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent
u = sp.Matrix([1, 0])
v = sp.Matrix([[1, sp.I], [0, 0]])
z = u.conjugate().T*v
gram = v.conjugate().T*v
row_rank_one = z.conjugate().T*z
suggested = sp.conjugate(row_rank_one)
actual_residual = gram-row_rank_one
suggested_residual = gram-suggested
assert actual_residual == sp.zeros(2)
assert suggested_residual == sp.Matrix([[0, 2*sp.I], [-2*sp.I, 0]])
assert sorted(suggested_residual.eigenvals()) == [-2, 2]
result = dict(u=sp.sstr(u), V=sp.sstr(v), z_row=sp.sstr(z),
    actual_Gram=sp.sstr(gram), correct_z_adjoint_z=sp.sstr(row_rank_one),
    correct_residual=sp.sstr(actual_residual), suggested_residual=sp.sstr(suggested_residual),
    suggested_residual_eigenvalues=[-2,2],
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    status='PASS exact phase-sensitive row-Gram control; proposed conjugation swap is false')
(HERE/'review-conjugation-control.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS exact row-Gram control; suggested conjugation swap gives indefinite residual, eigenvalues -2,+2.')
