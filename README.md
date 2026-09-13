# IBLP 良基性形式化

[![Lean proof verification](https://github.com/EgoFakeFantasy/IBLP-Wellfoundedness/actions/workflows/lean.yml/badge.svg)](https://github.com/EgoFakeFantasy/IBLP-Wellfoundedness/actions/workflows/lean.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

本项目已完成 `IBLP_wellfoundedness_zh.pdf` 定理 1.1 的 Lean 形式化：**`I3 → Acc Child root`**。主定理为 [IBLP.i3_wellFoundedAtRoot](IBLP/WellFoundedness.lean)，已完成完整构建、独立类型检查和传递公理审计。证明路线和最终证据见 [完成报告](COMPLETION_REPORT.zh.md)。

`Child` 由原 IBLP 展开程序定义，根有六行，零项为空表。完整证明保持全尾复制、原 q 阶梯、原生中行例外、规范化过滤后的冻结队列和原 I3。结论为原展开树良基；范围见 [语义锁定](SPEC_LOCK.md) 与 [阶段完成表](WORK_ITEMS.md)。

本仓库包含独立 Lake 项目、全部证明源码、分阶段计划和最终验证记录。依赖均为固定提交的公开 Git 仓库，不需要作者本机的相邻目录。

## 已实现的内容

最终完整复核覆盖 433 个项目模块、5037 个声明（180 个私有声明）、3846 个定理及 436 份源码哈希。主定理、所有可达图案的可访问性与无穷分支排除已通过内核检查；公理依赖只有 `propext`、`Classical.choice`、`Quot.sound`。完整证据归档为 `verification/stage9-final-*`。

| 模块 | 已证明或实现的内容 |
|---|---|
| `IBLP/Syntax.lean` | 原始行与模式、p/e/q、普通行型、proper 标记、饱和性；根的基本合法性、行型、空标记与饱和性 |
| `IBLP/Pointers.lean` | 行访问与倒数访问的存在性、p/q 严格下降、e 的正性所用列表界 |
| `IBLP/Trace.lean` | 精确到达目标的 p 输送；唯一性；`traceFrom_iff` 算法与关系等价 |
| `IBLP/Operations.lean` | 全尾复制、三类标记筛选、q 阶梯、native 中行例外、冻结扫描、原展开；根的首次复制与参数 1 展开 |
| `IBLP/NativeTermination.lean` | 合法普通行的 q 阶梯有输出；`e+1` 步数充分；来源界与严格递减 |
| `IBLP/ScanTermination.lean` | 插行长度、冻结过程长度不变、每事件消耗一个旧行；`scan_iff` 与有限运行关系等价 |
| `IBLP/Rank/I3.lean` | 非平凡自嵌入形式的 I3；由非平凡性推出临界点；复合幂和 application 的移位作用 |
| `IBLP/Rank/Restriction.lean` | 纯一阶公式相对化；任意较小秩（包括后继秩）上的限制初等性 |
| `IBLP/Rank/BoundedGraph.lean` | 实际集合图、函数性和相对初等性；从图恢复映射；后继秩上的临界点与序数边 |
| `IBLP/Rank/WeakAction.lean` | 任意集合输入的规范截断、截断交叠、域内取值、输出秩界及单图限制等式 |
| `IBLP/Rank/{Between,HierarchyGraph,BoundedHierarchy}.lean` | 不同秩之间的序数作用；后继秩的端点、顶层集合和层级保持 |
| `IBLP/Rank/{WeakTruncation,WordAction,WordRestriction,PrefixBounds}.lean` | (3.6)–(3.10)：截断交换、非空有限词、自然界、同时限制及前缀最小值公式 |
| `IBLP/Rank/{WeakAgreement,WeakEdges}.lean` | (3.11)：受限输入与全输入等价；左右复合、缩限和实际序数值读取 |
| `IBLP/Model/{TransitiveClass,Formula,Stage,Schemas}.lean` | 传递类、模型秩截段、逐公式语义、实际初等映射组成的阶段及有限公式输送 |
| `IBLP/Model/{Intersection,Powerset,Separation,Ordinals,Pair,Graph}.lean` | 内部幂集和分离、交集和配对、序数齐全；真实集合函数图与公式的等价 |
| `IBLP/Model/{HierarchyRec,UniverseHierarchy,HierarchyExistence,Hierarchy}.lean` | 实际内部累计层递归图；成员恰为模型中的低秩集合；内部层秩精确等于其指标 |
| `IBLP/Model/{HierarchyAlgebra,HierarchySequence}.lean` | 后继与极限层、实际截断封闭；递归图的完整取值和极限秩界 |
| `IBLP/Model/Replacement.lean` | 每个有限一阶公式的图选择、收集、强收集和唯一值替代 |
| `IBLP/Model/{Relativization,BoundedGraph,RankBridge}.lean` | 模型内集合结构的相对化；从完整真实图恢复初等映射；任意内部秩段的语言同构 |
| `IBLP/Model/{HierarchyImage,SuccessorImage,InternalGraphImage}.lean` | 实际初等映射保持内部累计层、后继序数及完整后继秩图，无附加端点等式 |
| `IBLP/Model/{BoundedMap,BoundedHierarchy,BoundedHierarchyLevels,RankHierarchySequence}.lean` | 内部有界映射的序数作用、端点及完整累计层保持 |
| `IBLP/Model/{InternalWeakAction,InternalRho,InternalWeakTruncation,InternalRestrictionAlgebra}.lean` | 任意模型输入的弱作用、截断交换及实际限制接入有限词代数 |
| `IBLP/Model/{SetRestriction,BoundedRestriction,BoundedComposition}.lean` | 较小后继秩上的真正初等限制、相容普通复合及完整值等式 |
| `IBLP/Model/{DefinableGraph,GraphOperations,GraphElementaryOperations}.lean` | 通过有限关系公式构造 M 中的限制图与复合图，并保持图初等性 |
| `IBLP/Model/Inaccessible*.lean` | 内部不可达有限公式、内部幂集语义、精确端点绝对性及不可达像保持 |
| `IBLP/Realization/{TraceWord,TraceGeometry,FiniteTraceRows}.lean` | 原 trace 去末点、原 p/e 几何、自然界计算与有限行资料扩张 |
| `IBLP/Realization/{InternalTrace,InternalTraceGraph,MarkCertificate}.lean` | 真实历史词及完整内部图、不可达自然界、载体行界与标记弱条件接口 |
| `IBLP/Realization/{BoundedMapGraph,RestrictedGraph,RootInaccessible,InitialGraph}.lean` | 实际图识别、内部限制图及同一原 I3 根图的内部化 |
| `IBLP/Realization/{RowGeometry,BoundedRealization,RootRealization,RealizedMark}.lean` | 完整有限实现、全部步边、原 I3 根证书，以及每条准确标记的实际词图、不可达自然界和全部载体界 |
| `IBLP/Model/{FiniteSets,FiniteGraph,CountableUnion,CountableImage}.lean` | 实际有限/可数集合与函数图、精确成员关系、秩界及初等像输送 |
| `IBLP/Encoding/{FiniteSyntax,FiniteImage,RealizationCode,RealizationImage}.lean` | 原图案与完整有限实现数据的单射集合编码、模型内存在、固定图案及像数据编码保持 |
| `IBLP/Model/{GraphCriticalPoint,WeakAgreementFormula,WeakAgreementImage}.lean` | 临界点和弱相等的真实有限公式、准确语义及初等输送 |
| `IBLP/Realization/{InitialCriticalPoint,MarkCertificateFormula,MarkFormula,FiniteDataImage}.lean` | 根临界点桥、准确历史词的弱证书有限公式，以及有限点/行图资料的初等像 |
| `IBLP/Model/SetSatisfaction*.lean`、`SetAssignmentDecoding.lean`、`SetTupleDecoding.lean`、`SetCodedAssignment.lean` | 任意实际集合结构的完整内部 Sat 集、单一有限递归公式、完整支持条件、存在唯一性与初等像；完整 GraphElementary 的单一有限公式 |
| `IBLP/Model/{SetSyntaxBooks,SetSyntaxBooksImage}.lean` | 六张实际语法表、秩界与无额外假设的初等像固定 |
| `IBLP/Extender/Collapse.lean` | 从已证良基、外延、集合式关系构造坍缩，证明单射、成员保持、传递性和唯一性 |
| `IBLP/Model/{BooleanOperations,Preimage,PairCoordinate}.lean` | 差集、图逆像与总化坐标关系的有限公式和绝对语义 |
| `IBLP/Extender/{DerivedMeasure,DerivedSystem}.lean` | 实际内部秩种子测度与完整集合函数；内部子集代数上的超滤规律 |
| `IBLP/Extender/{Projection,PairProjection,ProjectionComposition,FiniteSeeds}.lean` | 实际有界索引图、逆像相容、坐标与复合、任意有限共同种子及共同见证 |
| `IBLP/Extender/{TupleDomains,TupleMeasure,TupleSystem}.lean` | 完整有限积、原式 (4.2) 的真实内部测度、自动秩界、全部有限元数收集为同一个模型内系统集合 |
| `IBLP/Model/{GraphEvaluation,GraphWitness}.lean`、`IBLP/Extender/{Representative,FormulaTest,Witness}.lean` | 实际内部代表图、任意有限公式的真实测试集、内部选择见证和完整量词规律 |
| `IBLP/Extender/{RepresentativeEquality,UltrapowerAt,UltrapowerFormula}.lean` | 固定种子的实际商与成员结构、代表无关性、所有原生一阶公式的完整 Łoś 定理 |
| `IBLP/Extender/{ConstantRepresentative,UltrapowerEmbedding,FormulaPullback,UltrapowerTransition,UltrapowerCoherence}.lean` | 常值初等嵌入、实际投影拉回及初等过渡映射、复合规律和有限公共分量 |
| `IBLP/Extender/{IndexAgreement,CommonRefinement,GlobalTruth,GlobalRelation,GlobalQuantifiers,Ultrapower,GlobalLos,GlobalEmbedding,GlobalExtensionality}.lean` | 任意公共细化的比较独立性、实际全局商、完整原生 Łoś、分量与常值初等嵌入、过渡交换及外延性 |
| `IBLP/Model/{CountableRankBound,GraphRead,CountableRelation,RelationSections}.lean`、`IBLP/Extender/{NaturalTests,ReadIndex,CountableSeeds,CountableTests,WellFounded}.lean` | 实际可数公共种子、低秩可数测试关系、外部可数完备性及全局商的外部良基 |
| `IBLP/Extender/{BoundedRepresentative,SetLike,CollapsedModel,CollapsedLos}.lean` | 实际内部截取代表、前驱集合大小界、传递坍缩、坍缩语言同构与初等嵌入 |
| `IBLP/Model/{ElementaryNaturals,SequenceGraphExact}.lean`、`IBLP/Extender/{SequenceRepresentative,CountablyClosed}.lean` | 可数代表的实际内部合并、完整序列图、N 的外部可数封闭和下一模型阶段 |
| `IBLP/Rank/RootOwners.lean` | 六个 owner 的全部步边与临界点 |
| `IBLP/Rank/RootGraphs.lean` | 仅从 I3 得到六行根有界图；包含 θ 严格递增、初始基数性与不可达性 |
| `IBLP/Model/{UniformDefinability,UniformQuantifiers,UniformAtoms,HierarchyValueFormula,RankGraphFormula,UniformGraphOperations}.lean` | 真正有限的公式构造、量化、内部秩层与整张初等图的精确语义、无附加前提的初等反射 |
| `IBLP/Realization/{RowDataFormula,GraphWordFormula,TraceCertificateFormula,MarkPayloadFormula,CompletePayloadFormula,RealizationBelowFormula}.lean` | 完整实现存在性的有限公式，全部保存数据、准确轨迹、自然顶与弱证书的双向解码 |
| `IBLP/Realization/{MinimalBadTop,BelowFormulaReflection}.lean` | 外部最小坏顶及固定子图案公式反射，导出任意完整实现的可访问性 |
| `IBLP/Goal.lean`、`IBLP/WellFoundedness.lean` | 原主命题、`I3 → Acc Child root`、所有可达图案的可访问性及无穷分支排除 |

有限操作保留原 `Option` 接口。`Reachable.expand_total` 已证明 I3 下每个可达非零图案、每个参数都有展开输出。实际有限复制与冻结扫描的完整饱和实现闭包、原生过程总定义性和精确像顶下降全部完成。

最后反射采用每个固定有限图案的一条完整实现存在公式。先在源模型中取外部最小坏实现顶，再选一个实际坏子图案，将该固定子图案在像顶之下的完整实现存在性反射回来。完整实现、严格像顶比较和有限公式均已实际证明。此论证直接排除坏实现，无须将所有图案和外部坏性共同编码成一条统一对象语言 Bad 公式；完整说明见完成报告。

## 六行根的具体实现

令 θ 为 j 的临界序列，`g_s = Apply(j^s,j)`。第 1–6 行分别使用

`j, j, j ∘ j, g₂, g₂ ∘ g₂, g₄`。

对每行 r，将 owner 限制到 `V_(θ_e(r)+1)`，得到属于同一环境秩的集合图，目标是 `V_(θ_(r+1)+1)`。初等性对两端实际集合结构的全部一阶公式陈述；不是只核验有限 θ 点，也不要求后续图必须有全域 owner。

## 检查方式

安装 [Lean/Elan](https://github.com/leanprover/elan) 后运行。工具链由 `lean-toolchain` 固定为 Lean `v4.30.0`，依赖提交由 `lake-manifest.json` 固定：

```sh
git clone https://github.com/EgoFakeFantasy/IBLP-Wellfoundedness.git
cd IBLP-Wellfoundedness
lake exe cache get
lake build
lake env lean CheckMilestones.lean
lake env lean Audit.lean
```

运行与发布记录的逐字节对照检查：

```sh
python3 scripts/check_sources.py
```

有 PowerShell 7 的平台也可运行完整验收脚本：

```powershell
.\verify.ps1
```

脚本先确认每个项目模块都从根入口进入审计，再执行源码重新校验后的完整构建、`CheckMilestones.lean` 的独立类型检查、`Audit.lean` 的公理审计及源码禁用项检查。结果保存于 `verification/result.json`，包含确切源码 SHA256；完整输出保存于同目录的三个日志。

最终构建完成 1928 个构建项。`CheckMilestones.lean` 独立检查展开后的主类型 `I3 → Acc Child root`，并打印主定理与关键接口的传递公理依赖。具体时间、统计、原依赖提交和逐文件 SHA256 见 `verification/stage9-final-result.json`。

审计范围为导入 `IBLP` 后所有原始命名空间为 `IBLP` 的常量，含公开与私有辅助声明；检查定义与定理的传递公理依赖。允许项只有 Lean/Mathlib 通常使用的 `propext`、`Classical.choice`、`Quot.sound`。此次最终核验实际覆盖上述主定理；原规范对应另见 `SPEC_LOCK.md`。

## 依赖与参考

见 [DEPENDENCIES.md](DEPENDENCIES.md)、`dependency-lock.json` 与 [NOTICE.md](NOTICE.md)。GitHub Actions 从独立检出执行源码对照、完整构建、主定理类型检查与公理审计，并保存验证日志。原分阶段规划见 [形式化计划](docs/FORMALIZATION_PLAN.zh.md)。

## 许可证

本项目采用 **Apache License 2.0**，全文见 [LICENSE](LICENSE)，版权与第三方归属见 [NOTICE](NOTICE)。已保留上游 FullMarkedBLP 许可证及源码归属说明；各依赖继续遵循各自的许可证。
