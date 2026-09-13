import IBLP.Model.ElementaryCut
import IBLP.Model.InternalGraphImage
import IBLP.Realization.BoundedMapGraph

namespace IBLP.ModelStage
open FullMarkedBLP
universe u

/-- The first identity of manuscript (5.1), with the copied map recovered
from the actual image graph and with arbitrary internal set inputs. -/
theorem weakAction_image (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (rho sigma : Ordinal.{u})
    (graph : source.model.Element) (elementary : source.InternalGraphElementary rho sigma graph)
    (z : source.model.Element) :
    target.weakAction ((source.internalGraphElementary_image target j rho sigma graph).mpr elementary).toRankEmbedding (j z) =
      j (source.weakAction elementary.toRankEmbedding z) := by
  let image := (source.internalGraphElementary_image target j rho sigma graph).mpr elementary
  let oldRep := RepresentsBoundedMap.of_internalGraphElementary elementary
  let newRep := RepresentsBoundedMap.of_internalGraphElementary image
  have cutEq : j (source.rankInclude (Order.succ rho) (source.rankCut rho z)) =
      target.rankInclude (Order.succ (source.ordinalImage j rho)) (target.rankCut (source.ordinalImage j rho) (j z)) := by
    rw [source.rankCut_include, target.rankCut_include, source.cut_image target j]
  have oldEdge := (source.model.graphApplies_absolute graph
    (source.rankInclude _ (source.rankCut rho z)) (source.weakAction elementary.toRankEmbedding z)).mpr
      (oldRep.2 (source.rankCut rho z))
  have newEdge := (j.graphApplies_iff _ _ _).mpr oldEdge
  rw [cutEq, target.model.graphApplies_absolute] at newEdge
  apply Subtype.ext
  exact (newRep.1.2 (target.rankCut (source.ordinalImage j rho) (j z)).val
    ((target.mem_hierarchy _ _).mpr (target.rankCut (source.ordinalImage j rho) (j z)).property)).unique
      (newRep.2 (target.rankCut (source.ordinalImage j rho) (j z))) newEdge

end IBLP.ModelStage
