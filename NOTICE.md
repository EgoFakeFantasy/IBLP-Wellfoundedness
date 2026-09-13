# 上游代码说明

本项目参考和移植了 EgoFakeFantasy/FullMarkedBLP 的纯列表、扫描终止、公式与秩嵌入代码。具体来源在相关源文件注释及 DEPENDENCIES.md 中记录。原项目采用 Apache License 2.0；上游许可证副本保存在 `third_party/FullMarkedBLP-LICENSE.txt`。

扫描证明已改为本文的 IBLP 类型和任意扫描入口，并对本项目的实际定义重新编译。p/e/q 列表证明将基本合法性与普通行型分开。公式相对化参考 EgoFakeFantasy/RankElementarity，保留其对实际集合结构的语义解释，应用于任意较小秩。

上游的 FullMarkedBLP 最终良序结论没有作为本项目主定理调用。
