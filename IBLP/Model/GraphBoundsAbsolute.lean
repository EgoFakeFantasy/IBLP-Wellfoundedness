import IBLP.Model.GraphBoundsUnique

namespace IBLP.ModelStage
open FullMarkedBLP
universe u

/-- Across different ambient stages, the same complete graph still fixes
both ordinal endpoints, using exact hierarchy ranks and the endpoint edge. -/
theorem InternalGraphElementary.bounds_absolute {M N : ModelStage.{u}}
    {alpha beta gamma delta : Ordinal.{u}} {graph : M.model.Element} {graph' : N.model.Element}
    (left : M.InternalGraphElementary alpha beta graph)
    (right : N.InternalGraphElementary gamma delta graph') (same : graph.val = graph'.val) :
    alpha = gamma ∧ beta = delta := by
  have f := (M.model.function_absolute _ _ _).mp left.1
  have g := (N.model.function_absolute _ _ _).mp right.1
  rw [← same] at g
  have domains := functionGraph_domain_unique f g
  have ranks := congrArg ZFSet.rank domains
  rw [M.hierarchy_rank, N.hierarchy_rank] at ranks
  have source : alpha = gamma := Order.succ_injective ranks
  subst gamma
  refine ⟨rfl, ?_⟩
  have edge := right.endpoint_edge
  rw [← same] at edge
  have values := (f.2 alpha.toZFSet ((M.ordinal_mem_hierarchy _ _).mpr (Order.lt_succ alpha))).unique
    left.endpoint_edge edge
  simpa only [Ordinal.rank_toZFSet] using congrArg ZFSet.rank values

end IBLP.ModelStage
