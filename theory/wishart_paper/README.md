# Wishart formalization paper

日期：2026-10-16。

**当前修订尚未验收完成。** 请先读 [REVISION_STATUS.md](REVISION_STATUS.md)：164模块检查通过，但111条扩展公理审计未执行，最新PDF布局审查未完成。下述旧发布PDF和claims属于前一版本。

英文工作稿：**From Gaussian Samples to a Complex Wishart Minimum Law in Lean**。

- `main.tex`：完整正文与参考文献。
- `RESULTS.md`：已证成果、边界和论文取舍。
- `FOUNDATIONS_AND_RESEARCH.md`：概率论、信息论和Lean的基础解释、现有证明阅读路线及高价值研究计划。
- `claims.json`：论文主张到精确Lean声明、源码哈希及依赖的映射。
- `REPRODUCIBILITY.md`：锁定工具链、实际检查方法和实验复现。
- `SUBMISSION_READINESS.md`：arXiv官方要求对应的完成项和仍需人类完成的事项。

论文PDF在仓库 `output/pdf/wishart_formalization.pdf`。工作稿已完成并不表示已投稿或已通过独立语义审查。作者资料和公开仓库地址未填写，不猜测；PDF暂不列作者。

主线从实际样本概率律推导中心复2×2的密度和最小特征值分布，之后处理尺度与最弱模式对数速率中断。论文的主要价值在形式化证明链和可复用基础；经典公式不包装成新数学定理。
