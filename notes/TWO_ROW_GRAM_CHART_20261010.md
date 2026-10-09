# Bartlett 到 Gram：正首列能量域上的四实坐标换元

本卡开始 2026-10-10 01:55（Asia/Shanghai），截止仍为02:18。
接续已验收的6e462e8实际中心2×2 Bartlett/Gram推前，不重复证明独立性。

## 起手工具检索与准确采用

实际运行 verification/leansearch_lookup.ps1，各top-2：

1. `A triangular block matrix determinant equals the product of the diagonal block determinants`：
   命中 Matrix.twoBlockTriangular_det / det'，要求分块外零项并返回两个方块行列式积。
   当前导数矩阵本身下三角，不需要引入块索引。补查
   `Determinant of a lower triangular matrix is the product of diagonal entries`，
   命中 Matrix.det_of_lowerTriangular；本地已弃用，采用最新名
   `Matrix.det_of_isLowerTriangular (M : Matrix m m R) (h : M.IsLowerTriangular) :
   M.det = ∏ i, M i i`，Mathlib/LinearAlgebra/Matrix/Block.lean:397。
2. `Derivative of sqrt of positive real x is one divided by two times sqrt x`：
   命中 Real.hasStrictDerivAt_sqrt、HasFDerivAt.sqrt；直接采用后者：
   `hf : HasFDerivAt f f' x` 与 `hx : f x ≠ 0` 推出
   `HasFDerivAt (fun y => sqrt(f y)) ((1/(2*sqrt(f x))) • f') x`。
   正首列能量保证所需非零；不把零点包含进可微结论。
3. `Injective differentiable change of variables Lebesgue integral determinant derivative`：
   命中 MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul。
   本地 MeasureTheory/Function/Jacobian.lean:1183：有限维实范数空间上的addHaar测度μ，
   可测域s、逐点HasFDerivWithinAt f (f' x) s x、InjOn f s，任意非负测试g，
   则 `∫⁻ y in f '' s, g y = ∫⁻ x in s, ofReal |det(f' x)| * g(f x)`。
   直接采用；邻近的restrict_map_withDensity形式不需要另外复制。

锁定 Lean v4.35.0-rc2、mathlib e18afff334217588afc719a8b707b00d90521064、Apache2。
通过现成 hasFDerivAt_apply/pi、加乘幂导数及 LinearMap.det_toMatrix' 组装，
不重新证明一般微积分或测度换元。线上弃用名字不能未经本地核对直接采用。

## 精确图与数学作用

E=Fin4→ℝ（标准坐标Lebesgue测度），p=(S,x,y,E₀)，S>0。

```text
T(S,x,y,E₀) = (S, sqrt(S)x, sqrt(S)y, x²+y²+E₀).
T⁻¹(a,b,c,d) = (a, b/sqrt(a), c/sqrt(a), d-(b/sqrt(a))²-(c/sqrt(a))²).

DT = [ 1           0          0       0 ]
     [ x/(2sqrt(S)) sqrt(S)    0       0 ]
     [ y/(2sqrt(S)) 0          sqrt(S) 0 ]
     [ 0           2x         2y      1 ]
det DT = S.
```

明确证明左逆、正能量域注入性、实际Fréchet导数和LinearMap行列式。
twoRowGramChart_eq_BartlettGram_real 逐坐标核对，T恰好是上一卡
twoRowBartlettGram 的实坐标映射，非一个未与实际模型相连的玩具变换。
twoRowGramChart_lintegral_change 使用库内的一般换元定理得到具体乘S的非负积分式。
本域仅要求S>0；不把所有像点声称为正定Gram，正残差域还需另行处理。

## 数值与验收

先运行experiments/two_row_gram_chart_control.py，seed=202610100155，200000点。
对照显式逆和已知det=S，最大误差4.16e-15、7.11e-15；前1000点中心有限差分
与导数矩阵最大误差2.26e-09，退出码0。数值不是导数或换元证明。
非离散线性信息不等式，infoq Oracle/LP不适用。

实现调整：显式把下三角条件change成i<j的零项，避免OrderDual索引显示/推断；
积分目标显式消去lambda应用再重写det；复范数平方先作为独立等式正规化。
同一证明路线，未换弱陈述、未假设Jacobian或密度。
最终验收于 2026-10-09 18:12 UTC 前完成：

- `lake env lean -j1 JinWishartFormalization/TwoRowGramChart.lean` 退出码0。
- facade导入后 `lake build JinWishartFormalization --quiet` 主构建退出码0。
- `lake env lean -j1 checks/TwoRowGramChart.lean` 退出码0，5个回归覆盖具体四坐标
  数值映射、正域左逆、Jacobian、实际Bartlett实坐标对应及非负积分换元。
- 6条public theorem公理仅propext / Classical.choice / Quot.sound。
- 新源/检查无sorry、admit、native_decide或新axiom；git diff --check退出码0。

源编译保留不影响验收的simp/分支策略style警告，未为了消除警告反复换证明路线。
单线程验收；主构建约5分钟，未改lockfile或工具链，未启用付费服务、未推送GitHub。

## 补库边界与下一缺口

这解除中心2×2实际Gram推前到坐标Lebesgue积分所需的合法注入图/Jacobian依赖。
属于本地组装和具体模型换元，亦可用于复QR/Schur补；不声称首创或上游接收。
**尚不是实际Gram密度已证**：仍需把已证Gamma/Gaussian/Exp联合律接到该四坐标
Lebesgue密度、处理S=0零测边界及正残差支持，再用乘S换元得实际Gram密度。
之后仍缺Gram到有序谱的换元/角积分，非中心模型核，以及T3原刊边界/常数审查。
[需人工审查] Pi空间坐标volume、复实坐标识别、异常域和论文对应。
不同模型家族P4未完成，不称审查通过。
