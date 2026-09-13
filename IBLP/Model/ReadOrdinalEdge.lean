import IBLP.Realization.BoundedMapGraph
import IBLP.Model.InternalRho

namespace IBLP.ModelStage.RepresentsBoundedMap
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {graph : stage.model.Element}
  {k : stage.BoundedMap alpha beta}

/-- A saved ordinal edge is read by the actual weak ordinal action. Its
source-domain membership follows from the full graph itself. -/
theorem read_ordinal_edge (represented : stage.RepresentsBoundedMap graph k) {x y : Ordinal.{u}}
    (edge : ZFSet.pair x.toZFSet y.toZFSet ∈ graph.val) : stage.rho k x = y := by
  obtain ⟨input, inputValue, outputValue⟩ := (represented.graph_exact _ _).mp edge
  have inputEq : stage.rankInclude _ input = stage.ordinal x := Subtype.ext inputValue
  have value := stage.weakAction_on_domain k input
  rw [inputEq, stage.weakAction_ordinal] at value
  exact Ordinal.toZFSet_injective ((congrArg Subtype.val value).trans outputValue)

end IBLP.ModelStage.RepresentsBoundedMap
