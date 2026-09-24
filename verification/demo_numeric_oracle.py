"""数值反例预言机演示。

运行:  D:\\miniconda3\\python.exe demo_numeric_oracle.py
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import infoq


def target_form(claim):
    """把 "A >= B" 转成线性形式 A - B（即要求它 >= 0）。"""
    lhs, rhs = claim.split(">=")
    return infoq.parse(f"({lhs}) - ({rhs})")


def vars_of(form):
    vs = set()
    for S in form:
        vs |= S
    return vs


def show(title, claim, levels=2, samples=200_000):
    print("=" * 70)
    print(f"[{title}]")
    print(f"  命题: {claim}")
    form = target_form(claim)
    orc = infoq.Oracle(variables=vars_of(form), levels=levels, seed=7)
    out = orc.probe(form, n_samples=samples)
    print(f"  采样: {out['samples']} 个分布 (每变量 {levels} 个取值) + 局部精修")
    print(f"  最小间隙: {out['gap']:.6f}")
    if out["counterexample"]:
        print("  >>> 找到反例! 分布为:")
        print(orc.describe(out["pmf"]))
    elif out["tight"]:
        print("  >>> 不等式是紧的 (最小间隙 ~ 0)。取等分布如下, 可用于证明中的极值构造:")
        print(orc.describe(out["pmf"], thresh=0.05))
    else:
        print("  >>> 数值上远离为假 (注意: 这仍然不是证明)")
    print()


# 1. 次模性: 真且紧 -- 预期 gap ~ 0 (取等情形如 X=Y)
show("紧不等式", "H(X,Y) + H(Y,Z) >= H(X,Y,Z) + H(Y)")

# 2. "条件更多熵不减"是假命题: H(Z|X,Y) >= H(Z|X) -- 预期找到反例
show("假命题 (反例搜索)", "H(Z|X,Y) >= H(Z|X)")

# 3. 次可加性反方向: H(X,Y) >= H(X)+H(Y) 是假的 -- 预期反例
show("假命题 (反例搜索)", "H(X,Y) >= H(X) + H(Y)")
