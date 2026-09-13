# IBLP 项目约定

- 先看 README.md、WORK_ITEMS.md、SPEC_LOCK.md 和 verification/result.json；结果文件的源码哈希必须与当前代码对应。
- 主证明见 `IBLP/WellFoundedness.lean`；报告完成状态前须确认当前源码与最终完整验收哈希一致，不得用有限样例或过期审计代替主定理验证。
- 以原 PDF 的六行根、空零项、全尾复制、q 阶梯、冻结扫描和原 I3 为准。
- 原定义不允许的分支不得靠新增回退、删 mark 或运行时证书过滤补齐。
- 不新增数学公理、证明占位或 native_decide；保留已实际构造的完整内部 extender。
- 不把全部图限制为全域 owner 的限制；后续图须独立支持集合函数与相对初等性。
- 每个阶段用 verify.ps1 验证，并记录完成边界。修改上游前先检查其工作区；当前使用本地固定依赖，不运行 lake update。
