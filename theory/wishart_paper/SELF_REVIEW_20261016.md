# Codex 论文自审：是否可以直接提交

结论：**可以作为工作稿发给合作者征求意见；当前不建议直接作为最终版本提交 arXiv。** 这是证明实现与初稿写作者同一家族的自审，不是 AGENTS.md 所要求的独立 P4，也不是人工数学审阅。

## 仍需处理的事项，按优先级

| 优先级 | 问题与证据 | 投稿前处理 |
|---|---|---|
| 阻塞 | main.tex 的作者行仍为 `\author{}`。正文也明确称 working manuscript。 | 填写实际人类作者姓名并取得所有作者认可；单位与邮箱只填写真实且适用的信息。不从电脑用户名推断署名。 |
| 高 | 论文形式化贡献依赖源码，但附录仍说公开仓库/归档URL待补。当前几个本地ZIP不会自动成为读者可访问的证据。 | 提供固定公开版本，或将适当的代码与证据放入arXiv的anc附属文件。只上传 main.tex 的源码ZIP不能同时交付Lean工件。代码公开不是所有arXiv论文的统一强制条件；这里是本论文形式化主张的可评审性问题。 |
| 高 | 独立P4/人工语义审查未交付。先前Claude调用返回API 402，Codex自审不能填补不同家族审查记录。 | 让独立审查者核对方差、skew-product、换元、谱事件和记号，并处理真实意见。arXiv不要求先完成同行评审；这项约束来自本仓库P4及作者对内容的责任，不能冒称arXiv政策强制。 |
| 中 | 经典概率公式均非新发现；当前优势是实际样本到密度/最小值的形式化连接。一般维度G2仍开放。 | 维持“形式化案例研究”的定位，不以一般Wishart或新信息论定理宣传。明确项目新增接口与mathlib已有Gaussian/换元基础的区别；目前正文已基本做到。正式学术价值仍由领域审阅者判断。 |
| 中 | 工作流数字仅来自一个适应性指导的会话；权重digest与全部作者生成prompt未在当前工作流清单中完整固定。 | 可以核对38=2+29+7及五次无效P4，不能把它称为可精确重放的受控模型评测。现正文已声明不是benchmark；若将工作流提升为主要实验贡献，须另补协议、模型版本和完整试验材料。 |
| 提交操作 | 论文/代码许可、公开版本和最终arXiv元数据尚需人类作者决定。 | 作者自行选择有权授予的许可，确认标题/摘要/分类和账号要求。不由助手猜测身份或代选许可。 |

## 本次发现并已直接修正的两处表述风险

1. 原文“Gamma and exponential parameters are rates”容易让读者误读Gamma的第一个参数。改为Gamma(α,β)分别为shape和rate，Exp(r)为rate。数学与Lean声明没有变化。
2. 原文只称“unmodified determinant candidate”，未解释Lean中复行列式范数与原文实行列式比的对应。现在给出已证的中央2×2矩阵 Ψ(x)=exp(-x)[[x²+2x+2,x+1],[x+1,1]]，det Ψ(x)=exp(-2x)，det Ψ(0)=1；二者为正实数，因此本特例范数比与实行列式比一致。不将该说明推广到一般参数。

## 实际核对的数学链及结果

| 主题 | 实际核对依据 | 自审结果 |
|---|---|---|
| 单位复方差 | WishartProbability样本编码、实际CN缩放密度、Bartlett边缘律 | 实部/虚部各除sqrt(2)；CN系数π⁻¹与Gamma/Exp率约定相符。 |
| 随机首列方向 | twoRowUnitDirection、measurable_twoRowFiberCoordinates、twoRowRandomDirection_product_law | 显式可测性和skew_product连接固定纤维律，未把随机方向直接当确定子空间代入。零首列有单位方向fallback，Gram重构仍成立。 |
| Gram换元 | hasFDerivAt_twoRowGramChart、twoRowGramChartDerivative_det、实际密度推前 | 正域Jacobian为S，密度用1/S；与Bartlett的S/π因子相消。没有以目标密度为前提。 |
| 最小值事件 | TwoRowHermitianThreshold、TwoRowMinimumLaw、TwoRowSmallestEigenvalueCDF | 严格尾min>x对应PD平移锥，补集是min≤x；x≥0保证落在实际正支撑，负阈值CDF为0。 |
| 缩放 | TwoRowScaledMinimum | 振幅a>0，Gram倍率a²，方差v=a²，率2/a²；没有推广到任意协方差。 |
| Frobenius体积 | HermitianCoordinateMetric与坐标编码 | 对角实坐标权1、非对角实方向权2，2×2体积乘2、密度除2；显式框架体积有证明，内在体积的几何识别仍需人工确认。 |
| 非中心单列 | NoncentralOneColumnEnergy、T4NoncentralOneColumnAnyRows及2×1/3×1公式入口 | 实均值平方范数=2复Frobenius均值能量；渐近系数exp(-||M||²)/m!与球半径sqrt(2x)相符。2×1/3×1非中心公式保留λ>0和均值匹配，中心分支分开处理。 |
| 积分合法性抽查 | GaussianTwoColumnIntegration、NoncentralFourDimensionalGaussianCDF、NoncentralSixDimensionalMass等 | 两列Tonelli用于可测非负核；所读四/六维入口具有显式IntegrableOn或概率CDF极限条件。没有发现所读步骤遗漏这些前提；未覆盖全部传递依赖。 |
| 数值和来源 | 数值JSON、原工作流事件、主张清单与原文arXiv v2式(16)-(19) | 数值摘要与JSON吻合；中央特例行列式可直接核算。未核对期刊版每个公式，T3诊断仍不在正文。 |

在上述范围没有发现新的具体数学反例或会推翻主结论的错误。**这不是对165个模块全部证明体的人工认证。** 形式化内核通过仍不排除形式对象与外部模型解释之间的偏差。

## 文献与提交来源

重新读取并核对了Jin arXiv v2的式(16)-(19)、Affeldt/Cohen、Degenne及mathlib书目页面；未发现上述条目的新增错配。针对Wishart/Lean/Isabelle/Coq的检索没有返回可核实的同范围先行形式化，但不能据此证明“首次”；正文不作优先权声明。

- arXiv投稿总则：https://info.arxiv.org/help/submit/index.html
- 元数据说明：https://info.arxiv.org/help/prep.html
- 附属文件：https://info.arxiv.org/help/ancillary_files.html
- 审核与AI使用：https://info.arxiv.org/help/moderation/index.html
- 原文实际转录来源：https://arxiv.org/html/cs/0611007v2

作者对全文内容负责；arXiv审核不是同行评审。本自审不能承诺收录。下一步不需要为了投稿先补完一般G2，而是先关闭署名、可访问工件与独立语义审查这几项。
