"""Shannon 型不等式 LP 判定器演示。

运行:  D:\\miniconda3\\python.exe demo_shannon_lp.py
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import infoq


def show(title, claim, constraints=()):
    print("=" * 70)
    print(f"[{title}]")
    print(f"  命题: {claim}")
    if constraints:
        print(f"  约束: {', '.join(constraints)}")
    r = infoq.check(claim, constraints)
    print(f"  判定: {r.status}")
    print(f"  说明: {r.message}")
    if r.certificate:
        print("  证书 (目标 = 非负组合):")
        for coef, label in r.certificate:
            print(f"      {str(coef):>10}  x  {label}")
        for coef, k in r.constraint_coefs:
            print(f"      {str(coef):>10}  x  约束[{k}] (取负号使用)")
    print()


# 1. 次模性 (submodularity): H(X,Y)+H(Y,Z) >= H(X,Y,Z)+H(Y)
show("次模性", "H(X,Y) + H(Y,Z) >= H(X,Y,Z) + H(Y)")

# 2. 数据处理不等式 (DPI): X-Y-Z 马尔可夫时 I(X;Z) >= I(X;Z|Y)
show("数据处理不等式", "I(X;Z) >= I(X;Z|Y)", constraints=["X-Y-Z"])

# 3. 马尔可夫下 I(X;Z) <= I(X;Y)
show("DPI 推论", "I(X;Z) <= I(X;Y)", constraints=["X-Y-Z"])

# 4. 条件熵非负
show("条件熵非负", "H(X,Y|Z) >= 0")

# 5. Ingleton 不等式: 已知不能用 Shannon 型不等式证明 (非 Shannon 型领域)
show("Ingleton (预期 NOT_IDENTIFIED)",
     "I(X1;X2) >= I(X1;X2|X3) + I(X1;X2|X4) + I(X3;X4)")

# 6. 一个假命题: H(X,Y) >= H(X)+H(Y) 也不可证 (它本身就是错的, 见数值演示)
show("假命题 (预期 NOT_IDENTIFIED)", "H(X,Y) >= H(X) + H(Y)")
