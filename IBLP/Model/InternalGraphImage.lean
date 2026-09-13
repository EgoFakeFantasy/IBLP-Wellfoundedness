import IBLP.Model.RankBridge
import IBLP.Model.SuccessorImage

namespace IBLP
universe u

/-- 实际初等映射输送完整内部后继秩图；端点后继保持已经证明，无附加端点条件。 -/
theorem ModelStage.internalGraphElementary_image (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (alpha beta : Ordinal.{u})
    (graph : source.model.Element) :
    target.InternalGraphElementary (source.ordinalImage j alpha) (source.ordinalImage j beta) (j graph) ↔
      source.InternalGraphElementary alpha beta graph :=
  source.internalGraphElementary_image_iff target j alpha beta _ _ graph
    (source.ordinalImage_succ j alpha) (source.ordinalImage_succ j beta)

end IBLP
