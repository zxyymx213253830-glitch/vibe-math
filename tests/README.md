# tests/ — infoq 回归测试

用 Python 标准库 `unittest` 编写，**不引入任何新依赖**（本仓库声明"不依赖网络
即可运行全部演示"）。将来安装 pytest 后，这些用例可以被 pytest 直接发现并运行，
无需改写。

## 运行

```bat
cd /d "D:\vibe math"

:: 全部测试
D:\miniconda3\python.exe -m unittest discover -s tests -v

:: 单个文件
D:\miniconda3\python.exe tests\test_expr.py

:: 装了 pytest 之后（可选）
D:\miniconda3\python.exe -m pytest tests -q
```

## 覆盖内容

| 文件 | 覆盖 | 关键回归 |
|---|---|---|
| `test_expr.py` | 表达式解析、标量倍乘、命题/约束解析 | **`2*I(X;Y)`、`3/2*H(X,Y,Z)`、`2*(...)` 等文档承诺语法**（2026-09-26 之前全部抛 `ExprError`） |
| `test_shannon_lp.py` | LP 判定语义、证书精确性、已知结论表 | 每条 `PROVED` 的证书都用**精确有理数独立复核**；`NOT_IDENTIFIED` 的说明必须含"不代表命题为假" |
| `test_shannon_lp_status.py` | LP **四态状态机**（P2） | `UNVERIFIED` 降级、空证书合法性、求解器异常码、负系数拒绝、等式状态传播、`tol` 已移除 |
| `test_numeric.py` | 反例搜索、紧性、确定性 | 假命题必须被抓到反例；同种子结果可复现 |
| `test_converse.py` | converse 逐步机检 | 任一步非 `PROVED` 必须标记整条 converse 有洞；报告按状态分别计数 |

## 设计原则

1. **证书独立复核**：`test_shannon_lp.verify_certificate` 只使用公开 API ——
   把证书里的元素不等式标签重新 `parse` 回线性形式，按证书系数做非负组合，
   验证其结果精确等于目标。这把"证书已用精确有理数复核"从文档承诺变成了
   每次测试都实际执行的检查。
2. **语义纪律固化为测试**：`test_not_identified_is_not_a_refutation` 同时检查
   一个假命题和一个真而非 Shannon 型的命题，二者 LP 结果相同 —— 防止未来
   有人把 `NOT_IDENTIFIED` 误用成否证。
3. **区分证明与数值证据**：`TestOracleIsNotAProof` 只验证输出结构，不断言
   命题真伪。
4. **恒等式与不等式分开**：链式法则是线性恒等式（目标形式为 0），空组合
   就是精确证书；只有真正的不等式才要求非空证书。
