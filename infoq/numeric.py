"""infoq.numeric -- 数值反例预言机。

对任一线性形式（信息不等式的 LHS-RHS），在随机分布上找最小间隙：
  - 最小间隙 < 0        → 找到反例，打印具体分布；
  - 最小间隙 ~= 0       → 不等式是紧的，最小解指示取等的极端情形（对构造证明有用）；
  - 最小间隙 > 0 明显   → 数值上"远离为假"（注意：这不是证明，紧的假命题间隙也是 0）。
"""
from __future__ import annotations

from itertools import product

import numpy as np

__all__ = ["Oracle"]


class Oracle:
    """在 n 个离散变量（每个 m 个取值）的单纯形上评估信息表达式。"""

    def __init__(self, variables, levels: int = 2, seed: int = 1234):
        self.vars = sorted(variables)
        self.n = len(self.vars)
        self.m = int(levels)
        self.cells = self.m ** self.n
        self.rng = np.random.default_rng(seed)
        self._marg_cache: dict = {}

    # ---------- 基础设施 ----------

    def _marginal_matrix(self, S: frozenset) -> np.ndarray:
        """M 使 (边际分布) = M @ (联合分布按 cell 排平铺)。"""
        key = frozenset(S)
        if key in self._marg_cache:
            return self._marg_cache[key]
        cells = np.array(list(product(range(self.m), repeat=self.n)))  # (cells, n)
        var_index = {v: i for i, v in enumerate(self.vars)}
        proj = [var_index[v] for v in sorted(key)]
        if proj:
            weights = self.m ** np.arange(len(proj) - 1, -1, -1)
            mid = cells[:, proj] @ weights
            rows = self.m ** len(proj)
        else:
            mid = np.zeros(self.cells, dtype=int)
            rows = 1
        M = np.zeros((rows, self.cells))
        M[mid, np.arange(self.cells)] = 1.0
        self._marg_cache[key] = M
        return M

    def eval_pmf(self, form: dict, p: np.ndarray) -> float:
        """在单个分布上评估线性形式。"""
        val = 0.0
        for S, c in form.items():
            M = self._marginal_matrix(S)
            q = M @ p
            q = q[q > 1e-300]
            if q.size:
                val += float(c) * float(-(q * np.log(q)).sum())
        return val

    def gap_batch(self, form: dict, P: np.ndarray) -> np.ndarray:
        """在一批分布（B x cells）上向量化评估。"""
        total = np.zeros(P.shape[0])
        for S, c in form.items():
            M = self._marginal_matrix(S)
            Q = P @ M.T
            with np.errstate(divide="ignore", invalid="ignore"):
                ent = -np.where(Q > 0, Q * np.log(np.where(Q > 0, Q, 1.0)), 0.0).sum(axis=1)
            total += float(c) * ent
        return total

    # ---------- 反例搜索 ----------

    def probe(self, form: dict, n_samples: int = 100_000, refine: bool = True) -> dict:
        """随机采样 + 局部精修，返回 {gap, pmf, tight, counterexample, samples}。"""
        P = self.rng.dirichlet(np.ones(self.cells), size=n_samples)
        gaps = self.gap_batch(form, P)
        j = int(np.argmin(gaps))
        best_p = P[j].copy()
        best = float(gaps[j])
        if refine:
            best_p, best = self._refine(form, best_p)
        return {
            "gap": best,
            "pmf": best_p,
            "tight": abs(best) < 1e-6,
            "counterexample": best < -1e-9,
            "samples": n_samples,
        }

    def _refine(self, form: dict, p0: np.ndarray):
        from scipy.optimize import minimize

        def f(x):
            z = np.concatenate([[0.0], x])
            z = z - z.max()
            p = np.exp(z)
            p = p / p.sum()
            return self.eval_pmf(form, p)

        x0 = np.log(np.maximum(p0, 1e-12))[1:]
        res = minimize(f, x0, method="Nelder-Mead",
                       options=dict(maxiter=6000, xatol=1e-10, fatol=1e-12))
        z = np.concatenate([[0.0], res.x])
        z = z - z.max()
        p = np.exp(z)
        p = p / p.sum()
        return p, float(res.fun)

    # ---------- 输出 ----------

    def describe(self, pmf: np.ndarray, thresh: float = 0.01) -> str:
        """把联合分布打印成可读表格（只列概率 >= thresh 的 cell）。"""
        cells = np.array(list(product(range(self.m), repeat=self.n)))
        names = self.vars
        rows = []
        for k in np.argsort(-pmf):
            p = float(pmf[k])
            if p < thresh:
                break
            assign = ", ".join(f"{names[i]}={int(cells[k, i])}" for i in range(self.n))
            rows.append(f"    P({assign}) = {p:.4f}")
        return "\n".join(rows)
