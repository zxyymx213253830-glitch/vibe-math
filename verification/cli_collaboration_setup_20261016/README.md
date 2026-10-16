# CLI 安装与 Claude Code 恢复：2026-10-16

## 已实际验证

- **Qoder CLI 1.1.72**：从官方文档指向的 npm 包 `@qoder-ai/qodercli` 安装到 `D:\QoderCLI`。官方 PowerShell 安装脚本下载遇到 TLS EOF，未执行该脚本，改用官方保留的 npm 兼容安装方式。`qodercli --version`、`qoder --version`、帮助和登录命令均能运行。登录检查返回未登录；已启动官方浏览器授权流程，等待用户完成。未读取桌面端登录令牌。
- **ZCode CLI 0.16.5**：发现桌面应用已经包含官方 Node CLI `D:\Zcode\resources\glm\zcode.cjs`，无需第三方同名重打包。已在 `D:\ZCodeCLI` 配置 CMD/PowerShell 启动入口，版本、帮助和 `doctor --json` 均正常。最小模型调用提示独立模型配置缺失，尚未完成 GLM 推理验证。该旧运行时还会拒绝帮助中列出的 `--max-turns`，不能照抄帮助后宣称兼容。
- 两个入口目录均已加入**用户级** PATH，没有改动系统 PATH、已有 Claude 登录设置或 Lean 工具链。新终端可使用 `qodercli` / `qoder` / `zcode`；当前旧终端可用绝对路径。
- 现有 **Claude Code 2.1.283** 无需重新安装。最小请求、实际完整 P4 请求均已成功，后者退出0、耗时32.75秒。此前两次180/120秒超时仍原样保留，不用成功结果抹去失败。

## Claude Code 到底出了什么事

旧调用的现象是超时，而不是“程序没有安装”或已经证实的账号失效。配置默认模型字符串曾出现 `unrecognized_model` 警告。新调用显式使用文档支持的 `sonnet` 别名、禁用工具、无会话持久化、CI模式、流式JSON与有界超时，真实审查成功返回，CLI报告模型为 `claude-sonnet-5`。

**根因尚不能定论**：位置参数的最小请求能返回OK；随后在同样模式下，普通文件句柄作为stdin的最小对照也能返回OK。因此不能把旧失败武断归因于stdin、密钥、账号或网络中的某一个。现有代理与登录配置没有修改。CLI模型名/用量是该客户端与现有网关报告的，未独立验证后端模型权重身份；实际代理账单不由本记录保证。

已验证的只读调用形式：

```powershell
# 新打开的终端
$env:CI = 'true'
claude -p '只回复OK' --model sonnet --tools '' --strict-mcp-config `
  --no-session-persistence --output-format stream-json --verbose `
  --max-budget-usd 0.10 --permission-mode dontAsk

# 当前环境中也可以直接调用已经验证的入口
& 'D:\QoderCLI\qodercli.ps1' login
& 'D:\ZCodeCLI\zcode.ps1' doctor --json
```

不要把密码或令牌粘贴到聊天中；Qoder通过官方浏览器页面完成授权。ZCode CLI当前缺模型配置，不能把桌面登录成功等同于CLI配置完成，也未擅自复制桌面凭证。

## 收到的真实 P4 结果

`CLAUDE_P4_RESPONSE.md` 是真实返回文本，不是 Codex 代写；`claude-review-positional.stdout.jsonl` 保留原始输出。`review-manifest.json` 绑定四份实际提供的源码哈希与请求/回应。源码范围：

1. `GaussianRandomSubspaceLaw.lean`
2. `GaussianGramProjector.lean`
3. `GaussianOrthogonalProjectionLaw.lean`
4. `GaussianOrthogonalSplitLaw.lean`

另提供了锁定mathlib的skew-product源码片段。审查结论是在该范围内未发现阻断性数学错误，没有把固定子空间直接冒充随机子空间；同时重申实际满秩、维数、一般Jacobian/密度与方差模型对应仍需完成。审查者没有独立编译，也没收到接口检查文件或一般Bartlett代码，不能宣称覆盖它们。报告个别称谓（如“五个文件”、将可测函数称作“几乎处处可测”）不改变实际提供范围，实际源码参数是明确的 `Measurable`。

接口例子此前已单独编译PASS，但不因此扩大本次审查范围。未发现具体缺陷不等于一般Wishart定理完成，更不等于人工审查完成；**[需人工审查]** 标记保留。此次不改数学证明与论文，不重建、不更新投稿包、不向外部人员发送信息。

## 官方来源

- Qoder安装：https://docs.qoder.com/cli/installation
- Qoder认证：https://docs.qoder.com/cli/authentication
- ZCode官方源码与CLI说明：https://github.com/zai-org/ZCode/blob/main/README.en.md

网上存在多个不相关或第三方的同名 `zcode` 包，本次没有安装它们。官方独立CLI发行包下载入口尚未确认；这里配置的是现有官方桌面分发所带的CLI，不冒称独立成品发行包。
