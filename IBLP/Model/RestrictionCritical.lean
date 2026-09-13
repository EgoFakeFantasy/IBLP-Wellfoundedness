import IBLP.Realization.RestrictedGraph
import IBLP.Model.GraphCriticalPoint

namespace IBLP.ModelStage
open FullMarkedBLP
universe u

/-- An actual internal restriction retaining the critical ordinal has the
same critical point, including all smaller ordinal fixed-point witnesses. -/
theorem boundedRestrictionGraph_critical (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (graph : stage.model.Element) (k : stage.BoundedMap alpha beta)
    (represented : stage.RepresentsBoundedMap graph k) (delta : Ordinal.{u}) (included : delta ≤ alpha)
    (c : Ordinal.{u}) (hc : c ≤ delta) (critical : stage.model.GraphCriticalPoint graph (stage.ordinal c)) :
    stage.model.GraphCriticalPoint (stage.boundedRestrictionGraph graph k represented delta included) (stage.ordinal c) := by
  have old := (stage.graphCriticalPoint_iff_boundedMap represented c (hc.trans included)).mp critical
  apply (stage.graphCriticalPoint_iff_boundedMap
    (stage.boundedRestrictionGraph_represents ha graph k represented delta included) c hc).mpr
  constructor
  · intro fixed
    apply old.1
    rw [stage.boundedRestrict_val] at fixed
    exact fixed
  · intro eta below
    rw [stage.boundedRestrict_val]
    exact old.2 eta below

end IBLP.ModelStage
