import IBLP.Operations
import IBLP.Rank.I3

namespace IBLP

universe u

/-- 原展开树在六行根处良基；证明见 `IBLP.WellFoundedness`。 -/
def WellFoundedAtRoot : Prop := Acc Child root

/-- 主稿定理 1.1 的目标类型。不能把该命题当作新增公理导入。 -/
def I3WellFoundedStatement : Prop := I3.{u} → WellFoundedAtRoot

end IBLP
