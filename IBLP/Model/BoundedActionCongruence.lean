import IBLP.Model.WeakActionAbsolute
import IBLP.Model.InternalWeakTruncation
import IBLP.Rank.ActionCongruence

namespace IBLP.ModelStage
open FullMarkedBLP
universe u

theorem boundedCutAction_congr_graphs (stage : ModelStage.{u}) {alpha beta gamma delta : Ordinal.{u}}
    {k : stage.BoundedMap alpha beta} {l : stage.BoundedMap gamma delta}
    {graph graph' : stage.model.Element} (ha : Order.IsSuccLimit alpha) (hc : Order.IsSuccLimit gamma)
    (left : stage.RepresentsBoundedMap graph k) (right : stage.RepresentsBoundedMap graph' l)
    (same : graph.val = graph'.val) : stage.boundedCutAction ha k = stage.boundedCutAction hc l := by
  have bounds := left.toInternalGraphElementary.bounds_absolute right.toInternalGraphElementary same
  apply CutAction.ext
  · funext z
    exact Subtype.ext (representedWeakAction_absolute left right same z z rfl)
  · funext eta
    have values := representedWeakAction_absolute left right same (stage.ordinal eta) (stage.ordinal eta) rfl
    rw [stage.weakAction_ordinal, stage.weakAction_ordinal] at values
    exact Ordinal.toZFSet_injective values
  · exact bounds.2

end IBLP.ModelStage
