import IBLP.Realization.ActionGraphCongruence

namespace IBLP.ModelStage
open FullMarkedBLP
universe u

/-- A complete saved graph determines the entire bounded cut action,
even when the maps were reconstructed with different endpoint proofs. -/
theorem representedCutAction_congr {stage : ModelStage.{u}} {alpha beta gamma delta : Ordinal.{u}}
    {graph graph' : stage.model.Element} {k : stage.BoundedMap alpha beta} {l : stage.BoundedMap gamma delta}
    (left : stage.RepresentsBoundedMap graph k) (right : stage.RepresentsBoundedMap graph' l)
    (same : graph = graph') (ha : Order.IsSuccLimit alpha) (hg : Order.IsSuccLimit gamma) :
    stage.boundedCutAction ha k = stage.boundedCutAction hg l := by
  have values := congrArg Subtype.val same
  have bounds := left.toInternalGraphElementary.bounds_absolute right.toInternalGraphElementary values
  apply CutAction.ext
  · funext z
    exact Subtype.ext (representedWeakAction_absolute left right values z z rfl)
  · funext eta
    have ordinalValues := representedWeakAction_absolute left right values (stage.ordinal eta) (stage.ordinal eta) rfl
    rw [stage.weakAction_ordinal, stage.weakAction_ordinal] at ordinalValues
    exact Ordinal.toZFSet_injective ordinalValues
  · exact bounds.2

end IBLP.ModelStage
