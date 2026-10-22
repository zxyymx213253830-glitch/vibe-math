P4 mathematical route review ONLY. NOT final Lean source review or acceptance. Codex wrote the OPEN card and control scripts. Check only concrete mathematical faults: block shear DS=diag(A,N), smallest POSITIVE singular-value comparison with same rank index, and proposed sufficiency/necessity transfer using independent blocks. Do not cite uncertain literature or treat numerical controls as a proof. b=0/c=m are already separate ALL-moment branches; R=0 excluded. Never confuse singular value with its square. If an issue is not a gap say so, do not invent one. No tools. Report problems only.

# 下一任务：一般奇异模型最小正特征值逆矩（OPEN）

2026-10-22。当前已验收仍为665项、audit PASS、facade72真实exit0。本卡没有新增已证明命题，也没有新增Lean源文件。

## 精确候选

固定复矩阵B:p-by-n、M:m-by-n，Z:m-by-p为iid proper CN(0,1)，X=ZB+M。
记b=rank B，c=rank(M restricted ker B)，R=min(m,b+c)>0。
lambdaPlus指X^H X的最小**严格正**特征值，不是含结构零模态的列Gram最小值。

候选：若b=0或c=m，则所有非负实阶逆矩有限；否则b>0、c<m时

    E lambdaPlus^(-s) < infinity iff 0<s<abs(m-b-c)+1.

临界及更高阶的发散目标是非负ENNReal积分等于TOP，不能用总化Bochner积分表达无穷。R=0需单独定义，不能把不存在的最小正特征值当随机变量。仅固定参数；不宣称随B,M变化的一致估计。

## 已完成的预检

`experiments/singular_positive_minimum_preflight.py`，seed2026102211，每例400000样本，9个canonical例。8个Gamma闭式CDF对照、2个确定性谱下界、2个秩/结构零负对照，共12项通过。非中心、tall、wide及带无噪声列例的局部CDF斜率只是探索记录；低概率处样本噪声明显，不作为阈值证据或证明。结果和源码SHA保存在本轮run目录。

Qoder Qwen3.8-Max真实P1已于03:13:11UTC返回、exit0，工具关闭；原始回应完整保留。它正确指出主要缺口是确定性乘法比较和双边尾界。但以下文字不能采纳：

- 开头把列Gram最小值写成“minimum column norm”，两者不同。
- 我们的请求已明确排除b=0、c=m的有限阈值分支，回应却再次当作未处理反例。c=m给确定性正下界，不意味着整个随机谱变成确定性谱。
- 固定均值不会使独立高斯投影块失去独立性；要证明的是固定投影和协方差分解，不是声称固定M随机耦合了噪声。
- 奇异值与其平方的指数被混淆。平方最小奇异值CDF候选为x^kappa；奇异值CDF应为t^(2*kappa)。回应route2/3的指数及layer-cake公式不正确：完整逆矩尾公式应使用阈值t^(-1/s)，或等价适当变量代换；不能照抄其整条0到无穷积分。
- 固定参数下c的秩跳变不反驳命题；没有参数一致性要求。固定均值的连续高斯密度也不会产生额外低秩原子。
- 回应的未核实Bessel/universality文献不采用。本路线优先复用已验收的固定均值矩形高斯逆矩定理，不依赖新文献。

## 优先路线与缺口

1. 以固定可逆列变换、固定酉行变换，将分布化为

       D = [[A,0],[H,N]],

   A:(m-c)-by-b为proper独立高斯加固定均值，H:c-by-b为另一个独立高斯块加固定均值，N:c-by-c固定可逆。固定列变换仅改变非零奇异值的固定常数；必须形式化，不能假设其酉。
2. 右剪切S=[[I,0],[-N^-1 H,I]]满足DS=diag(A,N)。其逆只改变负号，范数可由1+||N^-1 H||控制。用非零奇异值乘积比较得到

       tau/(1+||N^-1 H||)^2 <= lambdaPlus(D)
         <= tau*(1+||N^-1 H||)^2,
       tau=min(lambdaPlus(A), sigmaMin(N)^2).

   此式当前是待核验路线，**未写成Lean证明**。c=0时应删除空N分量，而非把空矩阵最小值定义成0。R=rankA+c；比较用同一正秩序号，不能在不同维度取普通列最小值。
3. 充分性：控制多项式剪切因子的全部矩；独立块可分离期望。即使暂不使用独立性，也可用Holder选q>1使sq<kappa，获得严格阈值以下充分性。
4. 必要性与临界：需在独立事件||H||<=K（正概率）上用上界比较，将A的发散逆矩传给D。仅有一侧CDF指数或log斜率不够。A的wide情形须通过共轭转置接已验收tall固定均值定理，检查高斯law和最小正谱对应。
5. 然后才做实际源输运、正谱最小值可测性、ENNReal发散桥及最终字面目标检查/P4。不得以正确的canonical草图替代一般B,M的实际模型结论。

[需人工审查] 固定变换/分布、投影块独立性、非零奇异值序号、积分分离/Holder/ENNReal、零维分支及物理模型解释。以上所有新阈值内容仍OPEN。


CONTROL SOURCE SHA256 a583734de0017a48ed95c1fa9a3149a05ef5630809a4f62f094dd5e761a91ac7
"""Exact block identities plus numerical singular-value controls; no general proof."""
from pathlib import Path
import hashlib,json,sys,time
import numpy as np
import sympy as sp

seed=2026102212
rng=np.random.default_rng(seed)
checks=[]; cases=[]; start=time.monotonic()
def ratmat(a,b):
    return sp.Matrix(a,b,lambda i,j:int(rng.integers(-3,4))+sp.I*int(rng.integers(-2,3)))
def arr(A):
    return np.array(A.tolist(),complex).reshape(A.rows,A.cols)
for a,b,c in [(1,1,1),(2,1,1),(1,2,1),(2,2,1),(1,1,2),(2,3,2),(3,2,2),(1,0,1),(0,1,1),(1,1,0)]:
    for degenerate in [False,True]:
        A=sp.zeros(a,b) if degenerate else ratmat(a,b)
        H=ratmat(c,b)
        N=sp.diag(*range(1,c+1)) if c else sp.zeros(0,0)
        K=N.inv()*H if c else sp.zeros(0,b)
        D=A.row_join(sp.zeros(a,c)).col_join(H.row_join(N))
        E=A.row_join(sp.zeros(a,c)).col_join(sp.zeros(c,b).row_join(N))
        S=sp.eye(b).row_join(sp.zeros(b,c)).col_join((-K).row_join(sp.eye(c)))
        T=sp.eye(b).row_join(sp.zeros(b,c)).col_join(K.row_join(sp.eye(c)))
        assert D*S==E and S*T==sp.eye(b+c) and T*S==sp.eye(b+c)
        checks.append('exact-shear-and-inverse')
        R=int(A.rank())+c
        assert D.rank()==R and E.rank()==R
        checks.append('exact-rank-sum')
        L=1+np.linalg.norm(arr(K),'fro')
        assert np.linalg.norm(arr(S),2)<=L+1e-12
        assert np.linalg.norm(arr(T),2)<=L+1e-12
        checks.append('shear-norm-controls')
        if R:
            d=float(np.linalg.svd(arr(D),compute_uv=False)[R-1]**2)
            e=float(np.linalg.svd(arr(E),compute_uv=False)[R-1]**2)
            assert e/L**2<=d+1e-10 and d<=e*L**2+1e-10
            checks.append('same-positive-rank-index-sandwich')
        else:
            d=e=None
            assert D==sp.zeros(a+c,b+c)
            checks.append('rank-zero-excluded-minimum')
        cases.append(dict(a=a,b=b,c=c,degenerate_A=degenerate,rank=R,lambdaPlus_D=d,lambdaPlus_E=e,shear_bound=L))

# Known scalar 2-by-2 reference: product eigenvalues = eps^2, trace exact.
eps=.1; h=100.
tr=eps**2+h**2+1
exact_small=2*eps**2/(tr+np.sqrt(tr**2-4*eps**2))
actual=np.linalg.svd(np.array([[eps,0.],[h,1.]]),compute_uv=False)[-1]**2
assert abs(actual-exact_small)<1e-14
assert actual/eps**2<1e-3
checks.append('known-scalar-reference-and-failure-of-unit-comparison')
out=dict(status='PASS controls only; general block/singular-model proof OPEN',seed=seed,
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),checks=len(checks),
 check_labels=checks,cases=cases,negative_control=dict(eps=eps,H=h,lambdaPlus=actual,ratio_to_projected=actual/eps**2),seconds=time.monotonic()-start)
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status=out['status'],checks=len(checks),cases=len(cases),seconds=out['seconds'])))
