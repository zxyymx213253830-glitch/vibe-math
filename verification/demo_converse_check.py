"""converse 逐步机检演示。

命题: 若 X-Y-Z 构成马尔可夫链, 则 I(X;Z) <= I(X;Y)。
下面三步"证明"中第三步是故意放错的一步, 演示检查器如何抓住它。

运行:  D:\\miniconda3\\python.exe demo_converse_check.py
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import infoq

steps = [
    {
        "claim": "I(X;Z) <= I(X;Z,Y)",
        "constraints": [],
        "note": "链式法则: I(X;Z,Y) = I(X;Z) + I(X;Y|Z), 再用 I(X;Y|Z) >= 0",
    },
    {
        "claim": "I(X;Z,Y) <= I(X;Y)",
        "constraints": ["X-Y-Z"],
        "note": "I(X;Y,Z) = I(X;Y) + I(X;Z|Y), 马尔可夫性给出 I(X;Z|Y) = 0",
    },
    {
        "claim": "I(X;Y) <= I(X;Z)",
        "constraints": ["X-Y-Z"],
        "note": "!!! 这一步是错的 (方向反了), 演示检查器抓洞",
    },
]

results = infoq.check_steps(steps)
print(infoq.format_report(results))
