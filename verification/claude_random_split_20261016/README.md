# 新投影模块与跨模型协作：真实验收记录

用户授权采用 Claude Code、Qoder 或 ZCode 协作。实际找到已登录的 Claude Code 2.1.283。两次只读、禁用工具的调用分别于180秒与120秒超时，退出124，没有完整响应；首次配置模型同时产生 `unrecognized_model` 提示，第二次使用 CLI 帮助中支持的 `sonnet` 别名。代理主机无认证 HEAD 返回200，但这不能证明模型端点或额度正常。实际后端模型及调用费用未知，未收到语义审查意见。原始请求、源哈希、调用参数、时间和 stderr 均保留，未伪造审查。只检查凭证配置是否存在，未打印或复制令牌。

Qoder 与 ZCode 桌面安装均存在；PATH 与所检查的 bin 目录未发现可调用的对应 headless CLI，未操作 GUI、读取其登录令牌或注入内部消息。可在这些工具里打开 `COLLABORATION_REQUEST.md` 执行只读 P4 与下一步 P1，将真实结果写入独立 `EXTERNAL_RESPONSE.md`。当前该文件尚未交付；新代码的 P4 与 `[需人工审查]` 状态均保留。

## 实际形式化成果

Codex 新增 `GaussianGramProjector.lean`，十一条声明最终整叶检查退出0，公理仅 `propext, Classical.choice, Quot.sound`：

- 复矩阵的全定义 nonsingular inverse 在奇异分支也 Borel 可测。
- 显式 Gram 逆投影 `A (Aᴴ A)⁻¹ Aᴴ` 全局可测，投影向量在 A 和输入向量上联合可测。
- 该矩阵 Hermitian；Gram 行列式为单位时它固定原列、幂等并满足正规方程。
- 满秩时，显式矩阵恰为复列空间视作实子空间的真实正交投影。实/复内积转换通过逐坐标内积和实部求和核验，未混用不相同的 Lean 实内积实例。
- 定义 `totalGramColumnSpaceReal` 在满秩时取实际列空间，在奇异集取零空间，并证明其投影全局等于上述公式以及联合可测。**奇异集上的这个零空间通常不是原来的实际列空间。**

`GramProjectorIntegration.lean` 将这个具体子空间族与上一轮真实 Gamma 能量联合律实际拼接，检查退出0；不再把“投影可测”留为该接口的假设。但例子仍显式假设两侧几乎处处维数，不能据此声称实际 Gaussian 满秩或一般密度已证。

先执行 `experiments/gram_inverse_projector_control.py`：seed20261016，每种2048矩阵，尺寸3×1、5×2、6×3。独立 QR 投影对照与 Hermitian/幂等/固定列/正规方程残差的已知闭式零值均通过。该有限代数控制不是概率证明或一般维数证明，不新增谱 Monte Carlo 结论。

## 复现与范围

先运行上述控制。用**新的有效资源门**和已有工具 `tools/deepseek_prover/collaborative_check.py` 串行检查新模块，输出到 `gram-projector-final.txt`；`--library` 选择 `.tools/publication-revision-20261016/fresh-project-library`。再以本目录为 `--root`，模块名 `GramProjectorIntegration`，检查本目录的同名文件并输出 `integration-check.txt`。最后运行 `D:\miniconda3\python.exe verification/claude_random_split_20261016/audit.py`。

`audit.json` 绑定十一声明日志、新源码、olean、直接导入缓存、锁定工具链/依赖、接口检查及原始协作证据。中间的实际失败、类型类/内积实例错误、调试和 heartbeat 超限均留证；增大局部检查预算的尝试未通过，最终源码采用默认检查预算且无调试语句。叶子与接口检查分别报告，主入口与全构建本轮未运行。原论文及投稿包未改。

原请求清单里的 `prompt_sha256` 对应组装时的 UTF-8/LF 文本；Windows 保存产生CRLF，故另加 `prompt_file_sha256` 绑定实际文件字节，原值保留而未伪改。审计分别验证这两个哈希，不把不同换行编码当作同一字节快照。

下一核心义务仍是实际 Gaussian 前序矩阵满秩几乎必然与维数，然后是一般 Cholesky Jacobian、实际矩阵密度及 G2。测度、坐标方差与论文模型对应 **[需人工审查]**。旧 Step 审查不覆盖本轮新源码。没有启动自动循环、外部发信或远端推送。
