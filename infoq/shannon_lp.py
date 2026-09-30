"""infoq.shannon_lp -- Shannon 型不等式的线性规划判定器（ITIP 的数学内核）。

原理（Yeung 框架）：固定 n 个变量后，全部信息量都是 h(S)（S 为变量子集）的
线性函数。Shannon 型不等式锥由"元素不等式"有限生成：

    H(X_S | X_T) >= 0            （S 非空，T 与 S 不交）
    I(X_S ; X_T | X_U) >= 0      （S, T, U 两两不交，S, T 非空）

判定"目标不等式 t >= 0 是否 Shannon 型可证"等价于判定
t 是否落在  cone(元素不等式) + span(附加约束)  内，用 LP 判可行性。
LP 可行时，把解有理化并做精确有理数复核，输出人类可读的证明证书；
不可行时返回 NOT_IDENTIFIED（等价于 ITIP 返回 False，注意这不代表命题为假）。

``check()`` 返回四态（见该函数文档字符串）：PROVED / NOT_IDENTIFIED /
UNVERIFIED / SOLVER_ERROR。四态语义严格分离，绝不用数值可行性冒充证明。
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from itertools import combinations

import numpy as np
from scipy.optimize import linprog

from .expr import _add, _scale, parse_claim, parse_constraint, pretty

__all__ = ["ShannonResult", "check", "elemental_inequalities",
           "PROVED", "NOT_IDENTIFIED", "UNVERIFIED", "SOLVER_ERROR"]

PROVED = "PROVED"
NOT_IDENTIFIED = "NOT_IDENTIFIED"
#: LP 数值可行、但证书未能通过精确有理数复核。**这不是证明**，只是数值证据。
UNVERIFIED = "UNVERIFIED"
#: LP 求解器本身未正常结束（迭代上限/数值错误）。既不能证明也不能否证。
SOLVER_ERROR = "SOLVER_ERROR"

# scipy.optimize.linprog(method="highs") 的状态码
_LP_OPTIMAL = 0
_LP_INFEASIBLE = 2


def _all_subsets(xs):
    xs = list(xs)
    for r in range(len(xs) + 1):
        for c in combinations(xs, r):
            yield frozenset(c)


def elemental_inequalities(varnames):
    """生成变量集上的全部元素不等式，返回 [(系数字典, 标签), ...]。

    两族：H(S|T) >= 0（S 非空，T 不交）；
         I(S;T|U) >= 0（S,T,U 两两不交，S,T 非空；U 可为空）。
    I 族关于 S,T 对称，用规范键去重。
    """
    V = frozenset(varnames)
    out = []
    nonempty = [s for s in _all_subsets(V) if s]

    # ---- H(S|T) >= 0 ----
    for S in nonempty:
        tS = ",".join(sorted(S))
        for T in _all_subsets(V - S):
            tT = ",".join(sorted(T))
            if T:
                vec = {S | T: 1, T: -1}
                label = f"H({tS}|{tT}) >= 0"
            else:
                vec = {S: 1}
                label = f"H({tS}) >= 0"
            out.append((vec, label))

    # ---- I(S;T|U) >= 0 ----
    seen = set()
    for S in nonempty:
        rest1 = V - S
        for T in _all_subsets(rest1):
            if not T:
                continue
            rest2 = rest1 - T
            for U in _all_subsets(rest2):
                a, b = sorted([tuple(sorted(S)), tuple(sorted(T))])
                key = (a, b, tuple(sorted(U)))
                if key in seen:
                    continue
                seen.add(key)
                # I(S;T|U) = h(S∪U) + h(T∪U) - h(S∪T∪U) - h(U)
                vec = {S | U: 1, T | U: 1, S | T | U: -1}
                if U:
                    vec[U] = vec.get(U, 0) - 1
                tS, tT, tU = (",".join(sorted(x)) for x in (S, T, U))
                label = f"I({tS};{tT}|{tU}) >= 0" if U else f"I({tS};{tT}) >= 0"
                out.append((vec, label))
    return out


@dataclass
class ShannonResult:
    claim: str
    status: str                       # PROVED / NOT_IDENTIFIED / UNVERIFIED / SOLVER_ERROR
    target: dict                      # 目标线性形式（>= 0）
    message: str = ""
    certificate: list = field(default_factory=list)      # [(Fraction, 元素不等式标签)]
    constraint_coefs: list = field(default_factory=list)  # [(Fraction, 约束序号)]


def _rationalize_and_verify(target, elems, cons_forms, alpha, beta):
    """把 LP 解有理化，并用精确有理数运算复核组合恒等式。

    返回 ``(certificate, constraint_coefs)``；复核失败返回 ``(None, None)``。

    调用方必须区分两种"空"：

    * ``([], [])``   —— 精确成立的**空证书**。目标线性形式恒为 0 时
      （例如 ``I(X;Y) = I(Y;X)`` 这类恒等式）这是合法的、正确的证书。
    * ``(None, None)`` —— 复核失败。此时调用方**不得**返回 ``PROVED``。

    另外显式检查元素不等式的组合系数非负：``alpha`` 来自带 ``(0, None)``
    边界的 LP，数值上可能出现极小的负值；一旦有理化后仍为负，说明该解
    不可信，按失败处理。
    """
    used = []
    for i, v in enumerate(alpha):
        if abs(v) <= 1e-7:
            continue
        coef = Fraction(v).limit_denominator(5000)
        if coef < 0:
            return None, None
        used.append((coef, i))
    used_b = [Fraction(v).limit_denominator(5000) for v in beta]
    total: dict = {}
    for coef, i in used:
        for S, c in elems[i][0].items():
            total[S] = total.get(S, Fraction(0)) + coef * c
    for coef, f in zip(used_b, cons_forms):
        for S, c in f.items():
            total[S] = total.get(S, Fraction(0)) + coef * c
    total = {S: c for S, c in total.items() if c != 0}
    want = {S: c for S, c in target.items() if c != 0}
    if total == want:
        cert = [(coef, elems[i][1]) for coef, i in used]
        ccons = [(coef, k) for k, coef in enumerate(used_b) if coef != 0]
        return cert, ccons
    return None, None


def check(claim: str, constraints=()) -> ShannonResult:
    """判定信息不等式是否可由 Shannon 型不等式 + 附加约束推出。

    claim 形如 "I(X;Z) >= I(X;Z|Y)"；constraints 里可放马尔可夫链 "X-Y-Z"
    或等式约束 "I(X;Z|Y) = 0"。

    返回的 ``status`` 有四态，语义严格分离：

    ``PROVED``
        目标 = 元素不等式的非负组合 + 约束的线性组合，且该恒等式已用
        **精确有理数**复核。这是无条件的证明（在所给约束下）。
        目标恒为 0 时证书为 ``[]``，同样是有效的精确证书。
    ``NOT_IDENTIFIED``
        LP 已证明目标不在 Shannon 锥内（等价于 ITIP 返回 False）。
        **不代表命题为假**（Ingleton、Zhang-Yeung 型都在这一类）。
    ``UNVERIFIED``
        LP 数值上可行，但证书未通过精确复核（有理化失败或组合系数为负）。
        这只是数值证据，**不是证明**。
    ``SOLVER_ERROR``
        LP 求解器未正常结束。既不能证明也不能否证。

    .. note::
        历史上这里还有一个 ``tol`` 关键字参数，但它从未被使用，却让人
        误以为可以调节证明等级。已移除：证明等级只由精确证书决定。
    """
    op, lstr, rstr, lhs, rhs = parse_claim(claim)
    strict_note = ""
    if op in ("<", ">"):
        strict_note = "（注意：严格不等号的严格性 LP 无法判定，这里按非严格处理）"

    if op == "=":
        r1 = check(f"{lstr} >= {rstr}", constraints)
        r2 = check(f"{rstr} >= {lstr}", constraints)
        if r1.status == PROVED and r2.status == PROVED:
            return ShannonResult(claim, PROVED, {},
                                 "等式可由 Shannon 型不等式 + 约束证明。",
                                 r1.certificate + r2.certificate,
                                 r1.constraint_coefs + r2.constraint_coefs)
        # 任一方向未能核实，等式就不得判为已证明
        bad = [r for r in (r1, r2) if r.status != PROVED]
        statuses = {r.status for r in bad}
        if statuses == {NOT_IDENTIFIED}:
            st, why = NOT_IDENTIFIED, "有方向不在 Shannon 锥内"
        elif SOLVER_ERROR in statuses:
            st, why = SOLVER_ERROR, "LP 求解器异常"
        else:
            st, why = UNVERIFIED, "有方向未通过精确证书复核"
        return ShannonResult(
            claim, st, {},
            f"等式不可判定为已证明（{why}）：" + bad[0].message)

    if op in (">=", ">"):
        target = _add(lhs, _scale(rhs, Fraction(-1)))
    else:
        target = _add(rhs, _scale(lhs, Fraction(-1)))

    cons_forms: list = []
    for c in constraints:
        cons_forms.extend(parse_constraint(c))

    varnames = set()
    for f in [target] + cons_forms:
        for S in f:
            varnames |= S
    if not varnames:
        return ShannonResult(claim, PROVED, target, "平凡（不含任何信息量）。")

    elems = elemental_inequalities(varnames)
    subs = sorted({S for vec, _ in elems for S in vec}
                  | set(target)
                  | {S for f in cons_forms for S in f})
    idx = {S: i for i, S in enumerate(subs)}
    ncols = len(elems) + len(cons_forms)

    A_eq = np.zeros((len(subs), ncols))
    b_eq = np.zeros(len(subs))
    for j, (vec, _) in enumerate(elems):
        for S, c in vec.items():
            A_eq[idx[S], j] = float(c)
    for k, f in enumerate(cons_forms):
        for S, c in f.items():
            A_eq[idx[S], len(elems) + k] = float(c)
    for S, c in target.items():
        b_eq[idx[S]] = float(c)

    bounds = [(0, None)] * len(elems) + [(None, None)] * len(cons_forms)
    res = linprog(np.zeros(ncols), A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")

    if res.status == _LP_OPTIMAL:
        alpha = res.x[: len(elems)]
        beta = res.x[len(elems):]
        cert, ccons = _rationalize_and_verify(target, elems, cons_forms, alpha, beta)
        if cert is not None:
            msg = "可由 Shannon 型不等式 + 所给约束推出（证书已精确复核）。" + strict_note
            return ShannonResult(claim, PROVED, target, msg, cert, ccons)
        # 关键区分：LP 数值可行 ≠ 已证明。证书复核失败必须降级，绝不返回 PROVED。
        return ShannonResult(
            claim, UNVERIFIED, target,
            "LP 数值上可行，但证书未通过精确有理数复核（有理化失败或元素不等式"
            "组合系数为负）。这只是数值证据，不是证明。" + strict_note)

    if res.status == _LP_INFEASIBLE:
        return ShannonResult(
            claim, NOT_IDENTIFIED, target,
            "不在 Shannon 型不等式的锥内（等价于 ITIP 返回 False）。"
            "注意：这不代表命题为假，它可能需要非 Shannon 型不等式（如 Zhang-Yeung 型）。")

    return ShannonResult(
        claim, SOLVER_ERROR, target,
        f"LP 求解器未正常结束（scipy linprog 状态码 {res.status}："
        "1=迭代上限，3=无界，4=数值错误）。既不能证明也不能否证，"
        "请检查问题规模或求解器设置。")
