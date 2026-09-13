import IBLP.Realization.TraceWord
import IBLP.Model.InternalWeakAction
import IBLP.Model.BoundedHierarchy

namespace IBLP
open FullMarkedBLP
universe u

/-- Actual elementary successor-rank maps for the historical rows. The source
function will be instantiated by theta_e(r). Source limits and adjacent domain
inequalities are row facts, not assumptions about a composite trace word.
This interface alone does not assert that every resulting composite map has
an internal set graph; individual maps can be obtained from InternalGraphElementary. -/
structure InternalTraceRows (stage : ModelStage.{u}) (a : Pattern) (theta : Nat → Ordinal.{u}) where
  source : Nat → Ordinal.{u}
  source_limit : ∀ r, Order.IsSuccLimit (source r)
  map : ∀ r, stage.BoundedMap (source r) (theta (r + 1))
  source_gap : ∀ r p, predecessor a r = some p → theta p < source r
  adjacent_domain : ∀ r p, predecessor a r = some p → theta (p + 1) ≤ source r
  predecessor_value : ∀ r p, (hp : predecessor a r = some p) →
    (map r (stage.rankOrdinal ⟨theta p, Order.lt_succ_of_le (source_gap r p hp).le⟩)).val =
      (theta r).toZFSet

namespace InternalTraceRows
variable {stage : ModelStage.{u}} {a : Pattern} {theta : Nat → Ordinal.{u}}

theorem predecessor_ordinalAction (R : InternalTraceRows stage a theta)
    {r p : Nat} (hp : predecessor a r = some p) :
    (stage.rankOrdinalAction (R.map r)
      ⟨theta p, Order.lt_succ_of_le (R.source_gap r p hp).le⟩).val = theta r := by
  change (R.map r (stage.rankOrdinal _)).val.rank = theta r
  rw [R.predecessor_value r p hp, Ordinal.rank_toZFSet]

theorem endpoint_value (R : InternalTraceRows stage a theta) (r : Nat) :
    (R.map r (stage.rankOrdinal (endpoint (R.source r)))).val = (theta (r + 1)).toZFSet := by
  rw [stage.rankOrdinalAction_compat (R.map r), stage.boundedMap_endpoint]
  rfl

end InternalTraceRows
end IBLP
