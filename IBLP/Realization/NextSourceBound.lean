import IBLP.CrossingIndices
import IBLP.Model.ReadOrdinalEdge
import IBLP.Realization.FiniteWordImage

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

/-- The next source column maps above the entire natural bound of a mark
trace: its next target column lies strictly after the marked point. -/
theorem mark_bound_le_next_source_image (r : FiniteRowIndex a) {row : IBLP.Row}
    {mark source target : Nat} {rows : List Nat} (hr : rowAt a r.val = some row) (proper : row.ProperMark mark)
    (sourceAt : row.columns[row.columns.idxOf mark + 1 - row.step]? = some source)
    (h : FactorTrace a target mark rows) :
    (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound ≤
      (D.toFiniteTraceRows.toInternalTraceRows.actions.action r.val).rho (D.point source) := by
  obtain ⟨next, atNext, above, edge⟩ := IBLP.Row.next_target_edge (D.valid _ _ hr) proper sourceAt
  have value := (D.graph_represents r).read_ordinal_edge (D.edges r row hr (source, next) edge)
  change stage.rho (D.map r) (D.point source) = D.point next at value
  rw [D.toFiniteTraceRows.action_valid]
  change (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound ≤ stage.rho (D.map r) (D.point source)
  rw [value]
  obtain ⟨bound, nextValue⟩ := List.getElem?_eq_some_iff.mp atNext
  have inside := IBLP.Row.column_le_last (D.valid _ _ hr) (List.mem_iff_getElem.mpr ⟨_, bound, nextValue⟩)
  exact (h.bound_interval D.toFiniteTraceRows.toInternalTraceRows.actions).2.trans
    (D.point_increasing.monotoneOn (by change mark + 1 ≤ a.length + 1; have := r.property.2; omega)
      (by change next ≤ a.length + 1; have := r.property.2; omega) (by omega))

end IBLP.FiniteBoundedData
