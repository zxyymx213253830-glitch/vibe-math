2026-10-21 状态覆盖：以下为历史路线卡。平面stdGaussian乘积下全有限N多项式负部/绝对对数L1已验收（571绑定项）；properCN1乘积缩放及其后伪行列式谱积比较仍开放。不要把下文旧的小球界/一元/有限N缺口当成当前未完成项。详见WISHART_FINITE_GAUSSIAN_POLYNOMIAL_LOG.md。

# 下一张卡：高斯非零多项式的对数可积性 — OPEN

2026-10-20 10:13这一小时已闭合：noiseless-surjective行Gram偏移和一/二阶逆迹修正；
一般零模态偏移仅在显式hlog条件下闭合。不要把以下路线当证明。
Qoder general-rank-offset P1在90秒超时，没有有效分析回复；本卡是Codex定位，未获其审查。

## 精确缺口

固定B/M，q=min(m,rank stacked[B;M])，已证实际rank=q AE和EC/logr->q。
要无条件证明EC-qlogr->Elogpdet，需证明正谱对数绝对可积。
AE非零+L1不足：Uniform(0,1)上f(t)=exp(-1/t)有界且正，logf=-1/t不可积。
混合前检精确截断积分=-log eps验证了这一警示；不是高斯多项式反例。

## 优先分析卡

非零全纯复多项式P，在有限个独立CN1源上log|P|绝对可积。
正部由log^+|P|<=|P|和已有多项式L1控制；缺负部。
一元因式分解P=a product(z-root)给log^-|P|<=log^-|a|+SUM log^-|z-root|。
关键最小可复用引理：CN1的shifted root负对数矩存在一个独立于root的有限上界。
可由复Gaussian密度<=1/pi，得到P(|Z-root|^2<=x)<=min(1,x)，
再tail/layercake，或均值一致逆分数矩，得到负对数界。
已有ScalarGaussianComplexBridge提供真实均值CDF=复平面移位盘高斯密度积分，
尺度sqrt(2x)、密度1/(2pi) exp(-norm^2/2)；不要漏CN1的两实坐标/sqrt2。
下一步可先证明这个标量均值一致小球界。58项非中心chi-square/闭式/独立积分控制已通过，
但截至此卡撰写，该小球界、统一逆矩和负对数矩都还没有新增Lean证明。

多元路线按变量归纳：选择在最后变量中非零的最高次系数多项式；
其零集在其余高斯变量下null已由现有多项式零集定理覆盖。
对每个固定其余变量分别因式分解并用统一root界，再对系数递归。
不要未经证明选择可测的随机root：联合被积函数本身可测，
逐截面积分界可由每截面存在的有限root分解推出；随后Tonelli/Fubini仍需显式机检与人工审查。

## 从多项式到伪行列式仍需桥

已有最大秩固定平方压缩L X H见证，det压缩是非零全纯多项式候选。
还需确定性压缩行列式下界与全部正奇异值乘积的比较，常数依赖固定L/H；
或构造q阶Gram初等对称系数=所有q阶minor模平方和，借单个非零minor界log负部。
不能默认已有压缩见证已经证明了这个谱积不等式。

一旦logpdet L1，单谱log矩也可由trace L1补齐：
h_i=positiveSpectrumLog(lambda_i)，ell=SUM h_i；
h_i<=lambda_i、其他h_j<=lambda_j给|h_i|<=traceGram+|ell|。
这条有限谱绝对值界亦应单独写明，而非假定总和L1自动推出每项L1。
最后应用已证CorrelatedConditionalOffset，hlog仍是明确待交付的前提。
q0：空乘积1、logpdet0，应单列处理。

## 固定混合块对照

X=[A,0;D,I_s]，A:a×r,D:s×r，m=a+s,n=r+s。
r=a时detXX^H=detAA^H；均值噪声零空间作用秩s<m，没有统一正谱下界。
其实际Elogdet候选由sum digamma(1..a)控制，逆一阶通常不有限。
r>a时Schur多出I_s+D PkerA D^H，不能把D直接消去。
23项固定种子200000样本/已知闭式对照均通过，但不是上述一般定理证明。

[需人工审查] roots/Fubini/零集、Lebesgue-Gaussian密度/方差、谱积与原论文对应。
不增加未经核实文献引用，不刷新冻结投稿包。
