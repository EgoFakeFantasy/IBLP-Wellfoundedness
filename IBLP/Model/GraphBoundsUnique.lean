import IBLP.Realization.BoundedMapGraph
import IBLP.Model.BoundedHierarchy

namespace IBLP
open FullMarkedBLP
universe u

theorem functionGraph_domain_unique {d r d' r' graph : ZFSet.{u}}
    (left : ZFSet.IsFunc d r graph) (right : ZFSet.IsFunc d' r' graph) : d = d' := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, edge, _⟩ := left.2 x hx
    exact (ZFSet.pair_mem_prod.mp (right.1 edge)).1
  · intro hx
    obtain ⟨y, edge, _⟩ := right.2 x hx
    exact (ZFSet.pair_mem_prod.mp (left.1 edge)).1

namespace ModelStage
variable {stage : ModelStage.{u}}

theorem InternalGraphElementary.endpoint_edge {alpha beta : Ordinal.{u}} {graph : stage.model.Element}
    (h : stage.InternalGraphElementary alpha beta graph) :
    ZFSet.pair alpha.toZFSet beta.toZFSet ∈ graph.val := by
  have represented := RepresentsBoundedMap.of_internalGraphElementary h
  have edge := represented.2 (stage.rankOrdinal (endpoint alpha))
  have endpointValue := congrArg (fun o : OrdinalDomain (Order.succ beta) => o.val.toZFSet)
    (stage.boundedMap_endpoint h.toRankEmbedding)
  have same : (h.toRankEmbedding (stage.rankOrdinal (endpoint alpha))).val = beta.toZFSet :=
    (stage.rankOrdinalAction_compat h.toRankEmbedding (endpoint alpha)).trans endpointValue
  rw [same] at edge
  exact edge

/-- A complete elementary graph determines both its successor-rank source
and its target. The target is recovered from the image of the source
endpoint, not from an unsupported surjectivity claim. -/
theorem InternalGraphElementary.bounds_unique {alpha beta gamma delta : Ordinal.{u}}
    {graph : stage.model.Element} (left : stage.InternalGraphElementary alpha beta graph)
    (right : stage.InternalGraphElementary gamma delta graph) : alpha = gamma ∧ beta = delta := by
  have f := (stage.model.function_absolute _ _ _).mp left.1
  have g := (stage.model.function_absolute _ _ _).mp right.1
  have domains := functionGraph_domain_unique f g
  have ranks := congrArg ZFSet.rank domains
  rw [stage.hierarchy_rank, stage.hierarchy_rank] at ranks
  have source : alpha = gamma := Order.succ_injective ranks
  subst gamma
  refine ⟨rfl, ?_⟩
  have same := (f.2 alpha.toZFSet
    ((stage.ordinal_mem_hierarchy _ _).mpr (Order.lt_succ alpha))).unique
      left.endpoint_edge right.endpoint_edge
  simpa only [Ordinal.rank_toZFSet] using congrArg ZFSet.rank same

end ModelStage
end IBLP
