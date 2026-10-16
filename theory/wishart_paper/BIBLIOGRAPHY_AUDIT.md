# 参考文献核对与检索边界

2026-10-16修订。只把已核实的出处用于正文；书目信息核实不等于阅读全文或完成数学对应审查。

| 项目 | 已核实内容与来源 | 仍有边界 |
|---|---|---|
| Bartlett独立因子工作 | Cambridge原卷目录记载1933-09-29单独刊行，卷53页260–283；DOI 10.1017/S0370164600015637；卷年1934。正文写清两个日期。 | 不把历史优先权简化为本文首次，也不以此替代复数情形的具体证明 |
| Goodman复Gaussian | IMS/Project Euclid DOI元数据及Annals卷目录一致：34(1),152–177,1963；DOI 10.1214/aoms/1177704250。 | 全文抓取未成功；没有声称逐式对齐该文参考测度 |
| Edelman1988 | [作者MIT PDF](https://math.mit.edu/~edelman/homepage/papers/Eig.pdf)及[SIAM DOI](https://doi.org/10.1137/0609045)：9(4),543–560。 | 必须将实/虚部单位方差的约定转换到本项目单位复方差 |
| Edelman1991 | [出版社记录](https://www.sciencedirect.com/science/article/pii/0024379591900769)及作者MIT书目一致：LAA159,55–80；DOI 10.1016/0024-3795(91)90076-9。 | 作为经典最小值研究背景，不把实矩阵结论直接当本文复矩阵归一化 |
| Jin等期刊版 | [合著者所在大学记录](https://researchers.mq.edu.au/en/publications/mimo-multichannel-beamforming-ser-and-outage-using-new-eigenvalue/)：IEEE Trans. Commun.56(3),424–434,2008；DOI 10.1109/TCOMM.2008.060115。 | 期刊全文/逐式T3核对未完成。论文转录仍显式注明来自arXiv v2；T3诊断已移出正文 |
| mathlib论文 | [arXiv:1910.09336](https://arxiv.org/abs/1910.09336)实际重开核对标题、作者mathlib Community、2019年及v2。 | 不将旧综述当锁定版本Gaussian API文档 |
| 换元形式化 | [Gouëzel arXiv:2207.12742](https://arxiv.org/abs/2207.12742)。 | 正文只归属一般换元基础，不假定其替本项目建立所有坐标接口 |
| 概率核形式化 | [Degenne arXiv:2510.04070](https://arxiv.org/abs/2510.04070)，v2。 | 固定子空间到随机子空间的条件律仍开放 |
| Isabelle概率工作 | [Avigad/Hölzl/Serafin arXiv:1405.7012v4](https://arxiv.org/abs/1405.7012v4)核实作者、标题及Isabelle CLT范围。 | 只作跨系统概率基础比较，不称其包含Wishart |
| Coq/MathComp测度积分 | [Affeldt/Cohen arXiv:2209.02345v3](https://arxiv.org/abs/2209.02345v3)，JAR67文章28(2023)。 | 同上，不据不完整检索声称Wishart首次形式化 |
| arXiv AI政策 | [官方页面的具名章节](https://info.arxiv.org/help/moderation/index.html#policy-for-authors-use-of-generative-ai-language-tools)实际重开，段落涉及工具披露、人类作者责任、AI工具不列作者。 | 该政策不是对本文内容或录用的认证 |

检索尝试覆盖“Wishart formalization”、Isabelle/AFP、Coq/MathComp及Lean概率/随机矩阵关键词；没有得到可核实的同范围Wishart形式化条目。这是有限检索结果，不是不存在的证明。正文保留无“首次”的贡献声明。

直接复用的锁定mathlib资产：`HasGaussianLaw.indepFun_of_covariance_inner`、`IndepFun.map_prod_eq_prod_map_map`、标准Gaussian特征函数唯一性和通用换元。项目的固定投影声明是这些资产的特化/接口；论文贡献重点是实际样本编码、坐标密度/支撑和谱事件之间的连接。
