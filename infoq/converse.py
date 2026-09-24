"""infoq.converse -- converse（逆定理）证明的逐步机检器。

输入一串证明步骤，每步是一个信息不等式声明（可带马尔可夫约束），
逐步交给 Shannon LP 判定器，输出每步 PROVED / NOT_IDENTIFIED 的报告。
任何一步未通过即标记整条 converse "有洞"。
"""
from __future__ import annotations

from .shannon_lp import check

__all__ = ["check_steps", "format_report"]


def check_steps(steps) -> list:
    """steps: [{"claim": "A >= B", "constraints": ["X-Y-Z"], "note": "..."}, ...]

    返回 [(step, ShannonResult), ...]
    """
    results = []
    for st in steps:
        r = check(st["claim"], st.get("constraints", ()))
        results.append((st, r))
    return results


def format_report(results) -> str:
    lines = []
    n_bad = 0
    for i, (st, r) in enumerate(results, 1):
        cons = ", ".join(st.get("constraints", [])) or "(无)"
        lines.append(f"Step {i}: {st['claim']}    [约束: {cons}]")
        lines.append(f"  -> {r.status}: {r.message}")
        if r.status != "PROVED":
            n_bad += 1
        if st.get("note"):
            lines.append(f"  note: {st['note']}")
        lines.append("")
    if n_bad == 0:
        lines.append(f"结论: 全部 {len(results)} 步都通过机检（但语义是否与原命题一致仍需人工确认）。")
    else:
        lines.append(f"结论: {n_bad}/{len(results)} 步未被机检验证 —— 该 converse 作为证明有洞。")
    return "\n".join(lines)
