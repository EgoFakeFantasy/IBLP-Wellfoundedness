# 原 IBLP 六行根良基性：形式化完成报告

2026-09-13，原定目标已完成并通过 Lean 检查：

```lean
IBLP.i3_wellFoundedAtRoot : IBLP.I3.{u} → Acc IBLP.Child IBLP.root
```

证明位于 [IBLP/WellFoundedness.lean](IBLP/WellFoundedness.lean)。`I3` 是原定义的非平凡初等秩自嵌入假设；`Child` 是原有限展开程序的实际输出关系。根仍为六行，零项为空表。主定理没有额外的 extender 存在、实现存在、闭包或反射假设。

同时已证明 `Reachable.acc`：I3 下所有从原根有限可达的图案均可访问；以及 `i3_no_infinite_branch`：不存在从该根出发、每一步均为原 `Child` 的无限分支。结论覆盖原展开树良基性；未另行定义或证明键序上的良序性。

## 最终证明如何闭合

1. **从原 I3 建立完整根实现。** 六张实际图与八个序数点给出 `BoundedRealization initialStage root`。每张图属于相应模型，对完整后继秩结构具有全一阶初等性。
2. **证明原展开的完整闭包。** 内部 extender 从派生系统、完整 Łoś、外部良基和传递坍缩实际构造，像模型保持可数封闭。全部有限复制、冻结补全和原生事件保持所需语义。`expand_realization` 给出实际子实现，子顶恰为父最后显式点的初等像，严格小于父顶的初等像。
3. **将完整实现存在性变为有限公式。** 对每个固定有限图案 `a`，`UniformDefinable.realization_below a` 构造真正有限的纯成员关系公式，表达当前模型中存在顶低于给定序数的完整饱和实现。六个固定语法表参数在所有实际初等映射下保持不变。
4. **最小坏顶反射排除坏实现。** 若源模型有不可访问图案的完整实现，在所有这些实现的顶中取最小值 μ。选一个实际坏子图案 `b`，展开闭包给出像模型中顶小于 `j(μ)` 的完整 `b` 实现。对这个固定有限 `b` 使用第 3 步的公式，初等性反射回源模型，得到顶小于 μ 的坏实现，矛盾。故所有完整实现均可访问，应用第 1 步得到主定理。

跨模型的逐步像顶比较没有被当作同一模型内的无限下降。矛盾所需的源模型实现由实际有限公式反射获得。

## 公式覆盖与规划调整

| 完整语义条件 | 主要文件 |
|---|---|
| 实际内部累计层与后继秩层 | `Model/HierarchyValueFormula.lean`、`Model/RankGraphFormula.lean` |
| 序数点、递增性、内部不可达、行型、完整初等图、临界点及全部步边 | `Realization/RowDataFormula.lean` |
| 准确有限因子序列的整张复合图，排除多余非有序对元素 | `Realization/GraphWordFormula.lean` |
| 历史词真实端点值、计算得到的自然顶、完整弱证书 | `Realization/TraceCertificateFormula.lean` |
| 原配对源查找、原 trace 计算与去末点后的准确因子链 | `Realization/MarkPayloadFormula.lean` |
| 全部 proper 标记、饱和性及完整实现的双向恢复 | `Realization/CompletePayloadFormula.lean` |
| 有限见证整体量化、低于给定顶的完整实现存在性 | `Realization/RealizationBelowFormula.lean` |

原规划拟统一编码图案、坏性和最小坏顶。最终在元理论中选择坏子图案后，为该固定图案构造有限公式。公式随固定图案变化，但每次反射只使用一条有限公式，全一阶初等性足以支持。因此不再需要统一对象语言 `BadCode`/`MinBadCode` 总装；原主命题、完整实现条件和最小坏顶论证均保留，未增加主定理前提。

## 最终验证

最终完整验收：**2026-09-13 03:37:48 UTC**。

| 检查 | 结果 |
|---|---|
| 完整构建 | 1928 项构建任务通过 |
| 根导入覆盖 | 433 个项目模块 |
| 声明审计 | 5037 个声明，含 180 个私有声明 |
| 定理审计 | 3846 个定理 |
| 独立主类型 | `I3 → Acc Child root`，无辅助前提 |
| 传递公理依赖 | 仅 `propext`、`Classical.choice`、`Quot.sound` |
| 源码检查 | 无证明占位、额外公理或原生计算证明绕过 |
| 精确源码哈希 | 436 份 Lean 源码，最终复核无差异 |

证据：[结果与逐文件哈希](verification/stage9-final-result.json)、[完整构建](verification/stage9-final-build.log)、[独立类型与主定理公理输出](verification/stage9-final-milestones.log)、[全部声明审计](verification/stage9-final-audit.log)、[来源复核](verification/release-provenance.json)。

与阶段 4ac 已验收源码比较，先前源码仅根导入入口、独立检查文件和 `Goal.lean` 的说明文字发生变化。原运行规则、六行根、I3 定义、内部 extender 和有限展开闭包证明保持原样；最终新增 15 个模块。

## 复现与交接

在本项目目录运行：

```powershell
.\verify.ps1
```

脚本执行完整构建、独立类型检查、公开/私有传递公理审计、根导入覆盖和源码检查，记录精确 SHA256。Lean 为 `v4.30.0`；FullMarkedBLP 固定于 `832af28724c9897dfaf56248de662aee7b5a9b79`，mathlib 固定于 `c5ea00351c28e24afc9f0f84379aa41082b1188f`。十个依赖提交均与 `dependency-lock.json` 一致，配置见 [DEPENDENCIES.md](DEPENDENCIES.md)。

原 PDF SHA256：`6218983d5e52f4fc8cda17c3376aa813e29150902dcd88a2e2cd0d7cf687bf2c`，最终复核一致。上述原始验证在本地固定工作区完成。随后按用户要求整理为独立公开仓库，加入 Apache-2.0 许可证、固定 Git 依赖和 GitHub Actions 独立构建及公理审计；436 份已验收 Lean 源码保持逐字节相同。当前远程验证见仓库 Actions 页面。

