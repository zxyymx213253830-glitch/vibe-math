# T4：任意行数非中心单列 CDF 渐近（2026-10-09）

## 本卡目标和主线

用户明确：先完成金石等论文的定理形式化，OFDM 猜想暂缓。本卡只闭合
Theorem 4 的单列 CDF 渐近，不顺手扩展信息不等式、一般协方差或其他研究项目。

## 精确数学陈述及论文对应

令 `m>0`，`Z∈ℂ^(m×1)` 的元素独立且为单位复方差圆对称 Gaussian，
`M` 为任意确定性复均值，`φ=‖Z+M‖²` 为唯一 Gram 特征值。
定义 `F_M(x)=P(φ≤x)`，`λ=∑ᵢ‖Mᵢ₀‖²`，则

```text
lim (x→0+) F_M(x)/x^m = exp(-λ)/m!.
```

核对来源：[arXiv:cs/0611007v2 HTML 原文](https://arxiv.org/html/cs/0611007v2)，
Theorem 4 的 (29)–(32) 及 (54)。此处编号采用该 HTML 版本，不混用旧 PDF 记录。
取 `s=k=1,t=m`，`d₁=m-1`，`Γ₁(1)=1`、`Γ₁(m+1)=m!`，
故 `a₁=m exp(-tr Ω)/m!`，CDF 系数 `a₁/(d₁+1)=exp(-λ)/m!`。
本模型 `Ω=MᴴM`，其迹为 `λ`；实样本编码 `μ` 满足 `‖μ‖²/2=λ`。

正式定理：

- `noncentralOneColumnSmallestCDF_div_tendsto_factorial`：实编码参数版本。
- `noncentralOneColumnSmallestCDF_div_tendsto_frobenius`：复 Frobenius 参数版本。

两条左端都是实际标准 Gaussian 推前的 CDF，不是假设候选谱密度的抽象接口。
陈述没有 `hDensity`、可积性、归一化等待证结论作为额外前提；零均值包括在内。
`m=0` 明确排除，因为它不是论文的正维数单列模型。

## 证明与可复用库补充

1. `euclideanStdGaussianDensity_sub`：任意有限维实 Euclidean 空间中，
   `ρ(z-μ)=exp(-‖μ‖²/2+⟪z,μ⟫)ρ(z)`。
2. `gaussian_shiftedBall_integral_bounds`：半径 `R` 的中心闭球上，
   `|⟪z,μ⟫|≤R‖μ‖`；将密度点态上下界积分，夹逼系数为
   `exp(-‖μ‖²/2 ± R‖μ‖)`。不依赖 Wishart、复矩阵或具体维数。
3. 实际 CDF 的移位 Gaussian 小球桥给出 `R=√(2x)`。
4. 两侧除以 `x^m`，调用已有中心单列极限 `1/m!`，夹逼得到目标。

库复用：mathlib 的 `norm_sub_sq_real`、Cauchy–Schwarz、紧集上连续函数可积、
积分单调性和极限夹逼，均非本项目发明。新增的是组合这些基础的具体通用接口，
以及它到论文实际模型的证明。它避免为了这个目标继续逐维建立球面积分/Bessel 公式。

源码检索范围为项目锁定 mathlib 提交 `e18afff334217588afc719a8b707b00d90521064`：
全文搜索 `Wishart`、`Nuttall` 及本次新增两个定理名未命中。这只说明这些命名/分布层
未在本版本命中，不排除同义结果、其他 Lean 项目或未检索的新版本。
**不声称“别人没有做过”或已被 mathlib 合并。**

## 验证记录

数值实验 `experiments/noncentral_one_column_hard_edge.py`：固定种子 `20261009`，
行数 `1,2,3,5,8`，非中心参数 `0,0.5,3`，每模型 200000 个样本，共 3000000 个。
使用非中心卡方参考分布、独立 Poisson–Gamma 混合和中心 Gamma 对照，验证尺度、
有限阈值夹逼与小阈值系数。这不是信息量线性不等式，故 `infoq.Oracle` / Shannon LP
不适用，不能强行转译为熵变量问题。

- Python 运行退出码 0。
- 卡方/混合最大相对误差 `5.662e-15`。
- `x=1e-6` 时目标首项最大相对偏差 `1.000e-6`。
- 样本概率最大偏差 `1.868` 个标准误。
- 旧版本叶模块单独 Lean 检查退出码 0；公开通用引理后主工程构建退出码 0。
- 主入口回归检查退出码 0：任意行零均值、一行及两行特例全部通过。
- 五条公开定理的 `#print axioms` 均仅为 `propext`、`Classical.choice`、`Quot.sound`，
  无 `sorryAx` 或新增公理；新证明源码无 `sorry`、`admit`、`axiom`、`native_decide`。
- `git diff --cached --check` 退出码 0。首次回归文件有注释结束符及遗漏 filter 的语法问题，
  修正后重跑通过；正式数学定理及主构建未因此改动。

最终验收命令（Lean 工作目录为 `theory/jin_wishart_formalization`）：

```powershell
& 'D:\miniconda3\python.exe' experiments/noncentral_one_column_hard_edge.py
$env:ELAN_HOME = 'D:\vibe math\.tools\elan'
& 'D:\vibe math\.tools\elan\bin\lake.exe' build JinWishartFormalization --quiet
& 'D:\vibe math\.tools\elan\bin\lake.exe' env lean checks/T4NoncentralOneColumnAnyRows.lean
```

第一条 Python 命令从仓库根目录执行。回归从主入口导入，核验任意行零均值、
一行和两行边界，并打印全部五个新公开定理的依赖公理。

## 审查和剩余缺口

[需人工审查] 单位复方差到实标准 Gaussian 的 `√2` 编码、平移符号、
闭球与阈值事件等价、紧集可积性条件、右侧趋近及 `Ω` 的论文语义。
内核验收与数学建模对应是两个不同维度。当前可用模型均属同一家族，
未满足 AGENTS.md P4 的跨模型家族审查要求；不得标成独立审查通过。

本卡不证明密度渐近，不证明单列任意行 T1/T2 的 Nuttall 闭式，不证明多列 T1–4。
下一个关键模型缺口应进入**多列**：已有 `T3CentralTwoByTwoDensityInterface` 的
`hDensity` 仍是显式假设，需要从真实 Gaussian Gram 模型证明其有序谱联合密度，
而不是继续增加接受 `hDensity` 的接口。一般非中心还需谱 Jacobian、角变量积分及
归一化；T3 阶乘归一化问题须先对照原文裁决。
