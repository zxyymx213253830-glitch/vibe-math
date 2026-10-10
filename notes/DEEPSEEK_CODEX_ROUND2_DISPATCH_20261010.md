# 第二轮一小时协作调度

用户明确要求继续建立一个一小时任务。本轮已实际启动：

- 时间：2026-10-10 18:00:53–19:00:53，Asia/Shanghai。
- 精确截止：新运行目录state.json的`2026-10-10T11:00:53.606993+00:00`。
- 本地模型：Ollama `deepseek-prover-v2:7b`，初始主PID40168。
- 运行目录：`.tools/deepseek-hour/collaboration-round2-20261010/`。
- 队列和上下文：`tools/deepseek_prover/collaboration_round2/`。
- 新模块前缀：`JinWishartFormalization.DeepSeekCollaborationRound220261010`。
- 同一聊天heartbeat：`deepseek-wishart`，名称“DeepSeek与Codex：第二轮一小时协作”，
  已更新为ACTIVE，每五分钟调度，截止后留一次收尾唤醒并暂停。

DeepSeek主攻实际CN(0,1)密度、Bartlett产品密度及复到实密度。
Codex主攻现有Bartlett四实编码的volume对齐和Gram换元桥，并审查、对接。
新方向源文件约定`TwoRowBartlettCoordinateVolume.lean`，避免重做已经证明的
支持域、正性和Gram零边界。一般论文定理仍未闭合，不把辅助接口算作突破。

已证资产按原作者和核验哈希复制到新shared.json：上一小时两条候选密度函数
辅助、实际Bartlett正性、零边界、实际Gram行列式和重构等。旧目录原样保留；
本轮计数从零起，不把旧成果算作新证明。

本轮改进：每张卡只传必要依赖，缩短上下文；精确战术建议标记合作来源。
worker返回后先停止/卸载指定模型再释放计算锁，防止超时HTTP客户端留下
服务端生成，与Lean争抢资源。截止前来不及启动检查时保存未检查状态。
只停止自己的子进程和指定本地模型，不影响其他程序。

源码写作和检索可同时，Ollama与Lean按同一资源锁串行；新证明须保持原目标，
通过Lean内核及标准公理审计才可入库。[需人工审查] 测度/模型对应和跨模型
对抗问题审查；上一轮模型P4回应不合要求，不能沿用为已完成审查。

启动验证：Python语法检查通过，新状态RUNNING、首张卡已生成并进入LEAN_REVIEW，
stderr为空。模型输出仍是候选，不预先宣称数学成果。所有原始生成、报错、
语义审查、交流与归档会保留；每个可运行里程碑只提交自己文件，不推送远端。
