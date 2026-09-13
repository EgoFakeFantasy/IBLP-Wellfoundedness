import IBLP.Realization.BoundedRealization
import IBLP.CopyEntry

namespace IBLP
open FullMarkedBLP
universe u

/-- An actual saved row graph with all its endpoint, critical-point and
step-edge requirements, before placing the row in a new finite pattern. -/
structure RowGraphData (stage : ModelStage.{u}) (point : Nat → Ordinal.{u}) (owner : Nat) (row : IBLP.Row) where
  graph : stage.model.Element
  elementary : ∀ e, row.e = some e → stage.InternalGraphElementary (point e) (point (owner + 1)) graph
  critical : ∀ c, row.columns.head? = some c → stage.model.GraphCriticalPoint graph (stage.ordinal (point c))
  edges : ∀ edge ∈ row.edgePairs owner, ZFSet.pair (point edge.1).toZFSet (point edge.2).toZFSet ∈ graph.val

noncomputable def RowGraphData.repoint {stage : ModelStage.{u}} {point point' : Nat → Ordinal.{u}}
    {owner : Nat} {row : IBLP.Row} (G : RowGraphData stage point owner row)
    (valid : row.BasicValid owner) (shape : row.OrdinaryShape)
    (same : ∀ i, i ≤ owner + 1 → point i = point' i) : RowGraphData stage point' owner row where
  graph := G.graph
  elementary := by
    intro e he
    have eb := fromRight_le_last valid.1 valid.2.2.1 (Row.step_pos shape) he
    rw [← same e (by omega), ← same (owner + 1) le_rfl]
    exact G.elementary e he
  critical := by
    intro c hc
    have member : c ∈ row.columns := by
      obtain ⟨hi, value⟩ := List.getElem?_eq_some_iff.mp
        (show row.columns[0]? = some c by simpa only [List.head?_eq_getElem?] using hc)
      exact List.mem_iff_getElem.mpr ⟨0, hi, value⟩
    have cb := Row.column_le_last valid member
    rw [← same c (by omega)]
    exact G.critical c hc
  edges := by
    intro edge member
    have bounds := Row.edge_index_bounds valid member
    rw [← same edge.1 bounds.1, ← same edge.2 bounds.2]
    exact G.edges edge member

end IBLP
