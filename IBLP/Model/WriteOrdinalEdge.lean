import IBLP.Model.ReadOrdinalEdge

namespace IBLP.ModelStage.RepresentsBoundedMap
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {graph : stage.model.Element}
  {k : stage.BoundedMap alpha beta}

/-- An actual ordinal action equality gives a saved graph edge when its
input lies in the genuine source domain, including the endpoint. -/
theorem write_ordinal_edge (represented : stage.RepresentsBoundedMap graph k) {x y : Ordinal.{u}}
    (bound : x ≤ alpha) (value : stage.rho k x = y) : ZFSet.pair x.toZFSet y.toZFSet ∈ graph.val := by
  let input : stage.model.RankElement (Order.succ alpha) := stage.rankOrdinal ⟨x, Order.lt_succ_of_le bound⟩
  have inputEq : stage.rankInclude _ input = stage.ordinal x := rfl
  have applied := stage.weakAction_on_domain k input
  rw [inputEq, stage.weakAction_ordinal, value] at applied
  exact (represented.graph_exact _ _).mpr ⟨input, rfl, (congrArg Subtype.val applied).symm⟩

end IBLP.ModelStage.RepresentsBoundedMap
