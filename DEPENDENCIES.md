# 依赖与可复现范围

本项目为可独立克隆的 Lake 仓库，工具链和全部依赖均已锁定。

直接依赖为公开 Git 仓库 [FullMarkedBLP](https://github.com/EgoFakeFantasy/FullMarkedBLP)，固定于 `832af28724c9897dfaf56248de662aee7b5a9b79`。使用其秩结构、纯集合论公式、初等嵌入、application、临界点、不可达性和集合图等基础接口。其传递导入也包含旧 BLP 模块，但本项目目标、关系和根均由 `IBLP` 命名空间中的新定义给出。

`lake-manifest.json` 包含全部十个依赖的公开 Git 地址和精确提交；`dependency-lock.json` 提供简明对照。mathlib 固定于 `c5ea00351c28e24afc9f0f84379aa41082b1188f`，与已完成主证明时相同。构建无需本机路径；不要直接运行 `lake update` 改变这些版本。

RankElementarity 的 `RankReflection/FormulaRelativization.lean` 用作公式相对化的代码参考；本项目将其纯语言部分重新实现并扩展应用到后继秩，未把另一个 Lake 项目作为额外依赖接入。

已检查的 YesMetaZFC 目录有既有未提交修改。本项目没有修改该目录，也未将其作为 Lake 依赖。稿件引理 4.1 所需的完整内部 extender 已在本项目中实际构造，出口为 `Derivation.extend : InternalExtension D`。

主稿 SHA256 和规则来源见 `SPEC_LOCK.md`。最终原始构建和公理审计包含主定理 `IBLP.i3_wellFoundedAtRoot` 及无穷分支排除，见 `verification/stage9-final-result.json`。公开仓库的独立验证由 `.github/workflows/lean.yml` 执行；每次运行均重新构建并检查主类型和公理依赖。
