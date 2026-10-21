# 在本项目使用 SHEAF

已经完成 Windows 适配和首个小目标的试跑。最方便的用法是在当前 Codex 对话里说：

> 按 SHEAF 队列继续推进 Lean，先检查当前状态，并与 Qoder 合作审查。

Codex 负责读取任务卡、提出证明、串行编译和验收；Qoder 负责另一模型家族的对抗审查。无需你手工分配证明步骤。每次继续的工作范围以你的指令为准，不启动无限后台循环。

也可在 `D:\vibe math` 的 PowerShell 中查看：

```powershell
.\sheaf.ps1 status
.\sheaf.ps1 queue
```

`status` 检查目标锁和完成证据；`queue` 显示可推进的依赖节点。两者不会调用模型或启动 Lean。最初试跑完成时队列为空；2026-10-21 固定小时已验收有限 proper CN1 多项式对数可积性，并加入四个尚未形式化的子式/谱系数/一般奇异偏移目标。当前队列以 `coord/queue.md` 为准，详细路线见 `notes/WISHART_NEXT_PSEUDODET_CARD.md`。

需要复核当前两个目标时：

```powershell
.\sheaf.ps1 check
```

这只执行一次有界检查，沿用现有 `collaborative_check.py`、共享编译锁和固定 Lean/mathlib。它检查叶子源码及独立锁定的目标类型，**不会自动生成新证明，也不会仅凭编译通过就验收**。检查后须有对应源码的 Qoder P4、问题裁决、主入口编译和绑定审计，才能由协调者执行：

```powershell
.\sheaf.ps1 accept verification/sheaf_wishart/pilot-acceptance.json
```

旧验收文件不能用于新检查；修改了源码或依赖后需重做受影响的证据。目标陈述或定义锁变化会停止检查，不自动重锁或添加假设。遇到遗留锁，先检查持有者和相关日志；脚本不会删除其他进程的锁。

## 此次试跑

- 已核验标准复 Gaussian 闭圆盘概率不超过 `R^2/2`。
- 已核验实际 proper CN1 的 `1×1` 非中心 Gram 最小值 CDF 满足 `F_M(x) <= x`，对所有标量均值和 `x >= 0` 成立。
- 叶子、独立目标类型和总入口通过实际 Lean 检查；详细证据见 `verification/sheaf_wishart/pilot-acceptance.json`，数学边界与审查裁决见 `notes/WISHART_SHEAF_PILOT.md`。

这些是标量小球界，尚未完成通用高斯多项式负对数矩。密度、测度和物理方差对应仍标注 `[需人工审查]`。没有重建全部 Lake/mathlib，没有更新冻结论文或投稿包。

## 安装范围

来源为 [frenzymath/SHEAF](https://github.com/frenzymath/SHEAF)，固定提交见 `UPSTREAM.json`。复用了原版 `leanindex.py` 和 `dag_queue.py`，新增本地 Windows 协调器、声明/依赖锁和证据门禁。

没有运行上游 Linux Bash/tmux/fcntl 多代理启动器，也没有运行上游 comparator；目标类型比较由本地 Lean `Meta.isDefEq` 检查。当前按单个证明任务串行协调，保留已有的独立模型审查机制。不是完整上游集群部署，也没有后台服务或自动消耗额度的任务。

## 后续队列任务

已支持独立目标清单，不改原试跑锁。例如本轮新增的实际标量负对数目标：

```powershell
.\sheaf.ps1 status -TargetLock verification/sheaf_wishart/hour-20261020-1535/locks-scalar.json
.\sheaf.ps1 check -TargetLock verification/sheaf_wishart/hour-20261020-1535/locks-scalar.json
```

队列始终显示同一项目的全部目标；TargetLock 选择本次验证/检查的清单，不创建另一个项目。
工作中的固定小时协调者持有活动租约时，不要另起 check；脚本会拒绝。让当前 Codex 继续即可。
验收文件自带 target_lock、最终源码审查、类型比较及主入口证据；直接导入检查避免新叶子漏入主入口。

`verification/sheaf_wishart/hour-*/accept_*.py` 是对应时段的一次性证据准备记录，不能作为续跑入口。
本轮已为重复执行加上写入前拒绝检查，避免重复插入主入口或改变已绑定的审计清单。
新的工作时段应先取得新的用户授权、确认没有活动协调者，再使用当前队列和新的证据文件名。


## 2026-10-21 后续结果与 Linux 副本

当前610审计绑定项；除有限高斯多项式/固定压缩行列式对数L1外，一般固定矩形、奇异或零
B/M的总正谱对数L1和通用秩期望logdet偏移已验收，还包含正尺度处期望logdet的导数公式。
早先试跑章节为历史范围。完整边界见 notes/WISHART_HOUR_20261022_REVIEW_CN.md。
最新 Linux 副本位于 SheafBenchUbuntu 的 /root/wishart-sheaf-hour-20261022-0024，439个
输入文件逐哈希一致、71个DAG节点；当前目标已闭合，完整子集版Cauchy-Binet仍在闭包外延后。
之前388/405/409文件快照保留。它是源码工作快照，不是已经通过
Linux内核构建的green库。Windows仍是源码与编译证据的权威位置；没有迁移认证令牌。
后续Linux编译必须先准备同版Lean/mathlib并评审便携串行gate，不得绕过现有门禁。
