# 实际两列模型：随机首列方向、Bartlett 坐标与 Gram 推前

2026-10-10 01:42 起，本卡处于 01:18–02:18 授权窗口。
只推进中心 2×2 实际 Gaussian Gram 的随机方向分布依赖，不扩展 OFDM 或单列 CDF。
前卡固定方向的 Exp(1) 联合律已提交 896eb46，不重复计为本卡成果。

## 起手检索、采用及排除

实际调用 verification/leansearch_lookup.ps1（每查询 top-3）：

- `A measurable transformation preserving conditional probability measures preserves product measure skew product`。
  精确命中 `MeasureTheory.MeasurePreserving.skew_product`：
  `[SFinite μa] [SFinite μc]`，给定 `hf : MeasurePreserving f μa μb`、
  `hgm : Measurable (Function.uncurry g)` 和
  `hg : ∀ᵐ a ∂μa, (μc.map (g a)) = μd`，结论是
  `(a,c)↦(f a,g a c)` 把 μa×μc 推成 μb×μd。
  本地 Mathlib/MeasureTheory/Measure/Prod.lean:873–893，直接采用。
  普通 MeasurePreserving.prod 不能处理首列依赖函数；IsCondKernel.disintegrate
  需要额外条件核，当前直接逐纤维律足够，不采用。
- `Normalization of a vector to a unit vector is measurable`。
  命中 NormedSpace.normalize、norm_normalize 与 measurable_norm。
  本地 Analysis/Normed/Module/Normalize.lean：normalize x = ||x||⁻¹ • x；
  norm_normalize 要求 x≠0，norm_smul_normalize 对全部 x 重构原向量。
  采用这些已证代数接口，零点明确回退到 single 0 1，不假设归一化处处单位。
  可测性由现有 Measurable.ite、范数、逆及标量乘法接口组合，不重写归一化库。

实际另用 LeanExplore 查询 `Measurable skew product preserving fiber law`，top-1
返回相同 skew_product 完整源码；线上 aae61ae084c21995ee248964a81e3750ad0db2db。
精确符号字符串查询只返回 MeasurePreserving 定义，不能拿这个邻近结果代替目标定理；
改为数学语义查询后命中。top-2 仍是定义，不另采用。

本地锁定 Lean v4.35.0-rc2、mathlib e18afff334217588afc719a8b707b00d90521064，
Apache 2.0。既有 stdGaussian_euclideanEnergy_map_eq_gammaMeasure 直接用 k=2、
实维数4；不重证 Gamma 径向积分。实际概率模型及两列 split/join 都复用项目现成桥。

## 已写出的精确陈述

X,Y 是实际两列单位复方差中心 Gaussian。定义 a(X)=X/||X||（X≠0）；
X=0 时取 e₀。因此 a 是可测且处处单位，||X||a(X)=X 包含零点。
定义 W=<a(X),Y>，E=||Y-Wa(X)||²，S=||X||²。

- **整个 X** 与 (W,E) 的实际联合律为原 X 律 × CN(0,1) × Exp(1)。
- 实际样本空间中 (S,W,E) 的 law 为 Gamma(2,1) × CN(0,1) × Exp(1)。
- ||Y||²=|W|²+E，<X,Y>=sqrt(S)W，包含 X=0。
- 实际 `complexGram(complexSampleMatrix z)` 的 law 等于上述独立乘积测度
  在以下明确映射下的推前：

```text
             [ S          sqrt(S) W ]
G(S,W,E)  =  [ conj(sqrt(S) W)  |W|²+E ]
```

对应 `actualTwoRow_BartlettCoordinates_law` 和
`actualTwoRow_GramLaw_eq_Bartlett_pushforward`。
没有假设待证密度，也没有把 Gram law 定义为乘积后声称匹配实际样本。
skew_product 正式把所有固定纤维的已证共同 law 提升为随机首列依赖的 law；
不假设随机方向独立于 X，亦无需在本卡先证明 X≠0 几乎处处。

## 数值与验证

先写并运行 experiments/two_row_random_direction_control.py，seed=202610100142，
实际 2×2 Gaussian 样本200000，退出码0。
对照联合变换 `(1+t)^(-2) exp(-|z|²/4)/(1+s)`，最大偏差 1.037 SE。
实际 Gram 两项重构最大误差2.67e-15、8.66e-15，零方向回退单独核对。
这不是证明；infoq Oracle/LP 的离散线性信息量模型不适用于这个 Gaussian 律命题。

直接源码编译已退出码0，包含随机方向 law、实际 Gram 重构和 Bartlett 推前。
期间接口错配修复为显式 ℂ 实标量限制、明确目标可测类型及 Prod.mk.eta，
均保持同一证明路线与陈述；不通过换弱假设规避目标。
最终验收于 2026-10-09 17:54 UTC 前完成：

- `lake env lean -j1 JinWishartFormalization/TwoRowRandomDirectionLaw.lean` 退出码0。
- 导入主入口后 `lake build JinWishartFormalization --quiet` 退出码0。
- `lake env lean -j1 checks/TwoRowRandomDirectionLaw.lean` 退出码0。
  7 个回归覆盖零首列单位回退/Gram 重构、实际 Bartlett 与 Gram law，
  以及具体 W=I 的两共轭非对角项与第二对角能量3。
- 19 条 public theorem 的依赖公理仅 propext / Classical.choice / Quot.sound。
- 新源与检查无 sorry/admit/native_decide/新公理；git diff --check 退出码0。

保持单线程；源直接验收后只跑一次主构建和检查，无工具链/lockfile 改动。
未启用付费服务、未发送秘密或私有源码、未推送 GitHub。

## 作用、复用价值与最小剩余缺口

本卡解除过去“固定投影不能直接替代随机 QR”的实质依赖，并把中心2×2
实际 Gram 降至四个实的独立 Bartlett 坐标。可复用于复回归、Schur 补、
随机首列条件 Gaussian 和低维 Wishart 测度变换。
属于既有定理的本地组合与实际模型桥，不声称首创、上游接收或完成整篇论文。

仍未证明 Gram Lebesgue 密度或有序谱密度。下一最小卡：在 S>0 的坐标域上，
对 `(S,Re W,Im W,E)↦(S,Re(sqrt(S)W),Im(sqrt(S)W),|W|²+E)`
构造合法注入图与逆映射，导数行列式应为 S，再用现成 Jacobian 换元。
还需域边界/零测集、Gram→谱 Jacobian、角变量积分；非中心模型另外缺移位处理。
T1–4 一般多列公式及 T3 正式刊版归一化审查未闭合。
[需人工审查] 纤维可测性、零回退、共轭、方差和论文对应。
不同模型家族 P4 未完成，不称审查通过。
