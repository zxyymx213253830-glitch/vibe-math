"""Blahut-Arimoto 算法计算 BSC 信道容量，与闭式解 1 - H2(p) 对照。

这是 experiments/ 目录的模板: 任何容量/率失真的数值实验都按
"固定种子、数值迭代、与已知闭式解对照" 的格式写。

运行:  D:\\miniconda3\\python.exe blahut_arimoto.py
"""
import numpy as np


def binary_entropy(p):
    p = np.asarray(p, dtype=float)
    out = np.zeros_like(p)
    mask = (p > 0) & (p < 1)
    out[mask] = -(p[mask] * np.log2(p[mask]) + (1 - p[mask]) * np.log2(1 - p[mask]))
    return out


def blahut_arimoto(channel, tol=1e-12, max_iter=10_000, seed=0):
    """channel: P(Y|X) 矩阵, 形状 (|X|, |Y|)。返回 (容量, 输入分布, 迭代次数)。"""
    m, n = channel.shape
    q = np.full(m, 1.0 / m)          # 初始输入分布 (均匀)
    log_channel = np.log2(channel)   # 每行 log2 P(y|x) -- 全程用比特
    for it in range(1, max_iter + 1):
        # 步 1: 输出分布
        py = q @ channel                                   # (n,)
        # 步 2: 按 D[x] = KL(P(.|x) || py) 更新 q
        d = (channel * (log_channel - np.log2(py))).sum(axis=1)   # (m,)
        d = d - d.max()
        q_new = q * np.exp2(d)
        q_new /= q_new.sum()
        if np.abs(q_new - q).max() < tol:
            q = q_new
            # 容量 = sum_x q[x] * D[x] = I(X;Y)（收敛时即容量），单位比特
            py = q @ channel
            d = (channel * (log_channel - np.log2(py))).sum(axis=1)
            return float(q @ d), q, it
        q = q_new
    raise RuntimeError("Blahut-Arimoto 未收敛")


def main():
    rng = np.random.default_rng(seed=0)
    print("BSC 信道容量: Blahut-Arimoto 数值解 vs 闭式解 1 - H2(p)")
    print("-" * 60)
    worst = 0.0
    for crossover in [0.01, 0.05, 0.1, 0.25, 0.4]:
        channel = np.array([[1 - crossover, crossover],
                            [crossover, 1 - crossover]])
        cap, q, iters = blahut_arimoto(channel)
        closed = 1 - binary_entropy(crossover)
        err = abs(cap - closed)
        worst = max(worst, err)
        print(f"  p={crossover:<5}  BA={cap:.10f}  闭式={closed:.10f}  "
              f"|误差|={err:.2e}  迭代={iters:>3}  最优输入={np.round(q, 6)}")
    assert worst < 1e-9, f"数值解偏离闭式解: {worst}"
    print("\n[OK] 数值解与闭式解一致 (最大误差 < 1e-9)。")


if __name__ == "__main__":
    main()
