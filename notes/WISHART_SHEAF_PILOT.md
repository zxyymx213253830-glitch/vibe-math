# SHEAF Windows 接入与标量小球界验收

2026-10-20，用户授权直接操作 SHEAF 接入。固定上游提交
`6e5abd804e1b0c8d4626349e3508103c97452711`；未改 Lean/mathlib 版本。
旧固定小时轮已关闭，本次为单独有界安装试跑，heartbeat 保持 PAUSED。

## 形式化成果及边界

`ScalarUniformSmallBall.lean` 的两个声明现在有真实编译证据：

1. `stdGaussian_complex_closedBall_le_radius_sq_half`：任意复中心 μ、R>=0，
   `(stdGaussian ℂ).real (closedBall μ R) <= R^2/2`。
2. `actual_noncentralScalarCDF_le_threshold_uniform_mean`：任意固定 1×1 复均值 M、x>=0，
   实际 proper CN1 非中心 Gram 最小值的 CDF 不超过 x。

旧中断轮的失败检查及修正草稿保留；本次使用该修正源码的全新检查，未改弱目标。
先前固定标量控制 58 项已通过，数值控制不是证明。目标头、26 个依赖/定义/产物及独立
目标类型检查器在编译前锁定。叶子和类型检查日志见
`verification/sheaf_wishart/pilot-20261020T151023Z-3886ff.json`；两者真实 exit0，
类型比较输出 `SHEAF_TARGET_TYPES_EQ PASS`。只使用标准三公理；没有 sorry/new axiom。
主入口增加该模块，facade-53 真实 exit0。审计增加 2 项：547 -> 549
（547 theorem/instance + 2 构造），不是 549 个独立研究突破。

本次没有证明一般多维最小值一致小球界、通用多项式负对数矩或一般奇异模型的无条件
logdet 偏移。也没有完成原一般 T1–4 全映射、非中心联合谱密度 G2 或 T3 文献裁决。
全库 Lake/mathlib build NOT_RUN；冻结论文/PDF/投稿包/代码包不变。

## 最终源码 Qoder P4 的裁决

原始响应、prompt、最终源码快照和真实 exit0 receipt 全保留于
`verification/central_mixed_moments/*sheaf-smallball-20261020*`。
请求 Qwen3.8-Max，返回 qmodel_38max，tools disabled，没有独立编译。
不能把模型响应当作人工批准；以下是针对具体警报的源码裁决：

- 半径/方差警报：锁定的 `stdGaussian ℂ` 每个实坐标方差为 1，二维密度正是
  `(2*pi)^-1 exp(-norm^2/2)`。物理 proper CN1 另由两个实坐标除 sqrt2 构造。
  `scalarGaussian_shiftedBall_eq_complexBall` 明确给中心 `-sqrt2*M00`、半径
  `sqrt(2*x)`，所以圆盘界为 x；没有把缩放擅自吸入 stdGaussianℂ。
- 维度警报：实际声明结构固定 Fin1×Fin1，`by norm_num` 证明最小特征值定义所需
  正维度。没有宣称任意矩阵维度。响应所谓头部“Zero dimensions are intentional”
  并不在本模块头部，是把通用提示词当成源码；两个目标没有空维声明。
- 有限测度警报：`measureReal_def` 是 toReal 定义重写，无额外有限性前提。
  原测度和可测映射的推前均为概率测度，不会因 Jacobian 在零处退化而有无限质量。
  所用桥是已证测度等式，不是凭有限性猜测 change。
- 可测/积分比较警报：闭圆盘紧且可测，两个 IntegrableOn 已用连续性和紧性明确给出；
  全局点态上界更强于积分比较需要的界。内核检查已验证具体 API 参数。
- “单个均值”警报：M 是任意标量均值，右侧不含 M，正是一致界；导入标量桥
  没有隐藏的秩限制。独立类型比较也确认没有额外假设。
- Fubini/多项式零集警报：本模块复用密度与圆盘体积资产，没有新证明一般多项式零集
  或 Fubini 结论；RadialIntegration 提供所用圆盘体积/分析接口。

`[需人工审查]` 密度解释、圆盘体积、实坐标方差和物理 CN1 模型对应仍需人工核对。
上述裁决解决具体源码警报，不撤销人工审查义务。

## Windows 协调器审查

原版 SHEAF lexer/DAG scheduler 未改动；原 Linux 启动器、tmux、fcntl、landing 脚本
和 comparator 未执行。本地类型比较是独立字面目标的 Lean Meta.isDefEq，不冒称运行
了上游 comparator。没有安装/启动 WSL 或新的后台服务。

协调器的首次 Qoder P4 发现/提示的健壮性问题已落实：损坏锁的清理不能遮蔽原异常、
拒绝 null 类型证据、检查期间源/目标锁变化即失败、按锁声明映射 DAG 节点、过期完成
证据重新排队。完整源码先有真实 Qoder P4（`p4-adapter-final*`）；文字锁补丁另有最终 `p4-adapter-v2*` 审查及哈希绑定。
17 个无 Lean/无模型回归检查通过，覆盖目标增假设、定义变化、重复领任务、异主/损坏锁、
缺依赖/环、无 sorry 仍未编译、陈旧完成证据、STOP、活动协调者和异常租约关闭。

最终审查没有在约定的本地可信配置场景中找出错误验收实例。原响应中
“--no-sorry semantics”不是本工具的真实选项声明：拒绝占位依赖源扫描、日志和公理审计。
现存 compute.lock 与 STOP 即使过期也阻止新检查，需要先人工检查持有者；这是有意
失败关闭，不自动接管。主操作 O_EXCL 锁与底层 compute.lock 分别串行协调和编译。
新证据文件名使用 UUID，预存在即拒绝；未设计成对恶意本地篡改者有数字签名的证明系统。
哈希用于检测意外陈旧/漂移，不是外部可信时间戳或密码学执行证明。

源码与证明工作由 Codex 完成，Qoder 只做对抗审查，不把同一模型自审计作 P4。
当前状态、运行方法和后续边界见 `sheaf/wishart/README.md`。

## 文字锁解析补丁（保留前后记录）

首次验收后复查发现，上游 commands 的 statement 字段把 `(m := 1)` 截成了证明起点。
这不影响此前独立字面命题的 Lean 类型检查，但不足以作为完整的文字陈述锁。
原版 lexer/DAG 文件仍不修改，本地 complete_statement 对括号进行配对，只在顶层 `:=`
处分离证明；额外回归覆盖命名参数之后的结论变化，以及 null 类型证据/超时 P4 的拒绝。
原始 v1 目标锁归档 `verification/sheaf_wishart/target-lock-v1-before-parser-fix.json`。
协调者明确审阅修订 v2 完整头部，与未改的独立字面目标一致；没有增加假设或改变结论。
新锁建立后重跑叶子和完整类型检查，旧检查/首次验收记录保留但不再作为当前验收证据。
总入口源码及 Lean 证明均未改变，沿用已通过的 facade-53，避免无变化重复编译。

最终 v2 P4 提出的字符串括号警报是误读：complete_statement 只遍历 kind=code 的字符，
字符串段经 continue 整段跳过，新增带未配对括号和 := 的字符串默认参数回归通过。
P4 所称共享 with 中前一个 context 尚未进入也不符合 Python 语义；前置 context 已进入，
后续失败会逆序退出。accept 不需要启动新编译，旧任务 claim 若遗留需检查但不抹除已有
可验证的证据。瞬时文件读取失败只拒绝验收；没有写完成标记。DAG 外部同时修改不属
多协调者支持范围，公共变更路径由 operation.lock 串行，重复声明/缺依赖/环拒绝。
占位警报也承认最终 audit 拒绝，check 的“成功”只表示局部检查，不是验收状态。
时限由实际 gate 执行，adapter 未另建第二 runner；没有承诺抵抗底层 gate 自身的任意故障。
Windows Path 的路径相对比较采用 Windows 语义，并非响应所称一律区分大小写；特殊不一致
路径即保守拒绝。原回复完整保留，不按其“concrete defects”措辞认定不存在的故障。
