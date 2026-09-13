import IBLP.Realization.NextSourceBound
import IBLP.Realization.RawCopyPointsExact

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

/-- The literal high-filter next-source image lies at most at the old
control minimum. Reading its actual copied row edge proves (5.8). -/
theorem highCopy_input_bound (nonempty : 0 < a.length) {b : IBLP.Pattern} {last row : IBLP.Row}
    {minimum p mark nextSource target : Nat} {rows : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (r : FiniteRowIndex b) (hr : rowAt b r.val = some row) (markProper : row.ProperMark mark)
    (nextAt : row.columns[row.columns.idxOf mark + 1 - row.step]? = some nextSource)
    (screened : nextSource ≤ minimum) (h : FactorTrace b target mark rows) :
    (h.word (D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows.actions).bound ≤
      ((D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows.actions.action r.val).rho
        (D.point minimum) := by
  let copied := D.rawCopyData nonempty proper copy hlast hm hp
  have lastAt := IBLP.getLast_rowAt hlast
  have mp := IBLP.Row.minimum_le_column (D.valid _ _ lastAt) hm (IBLP.fromRight_mem hp)
  have pn := IBLP.fromRight_le_last (D.valid _ _ lastAt).1 (D.valid _ _ lastAt).2.2.1 (by omega) hp
  have length := IBLP.rawCopy_length copy hlast hp
  have points : copied.point nextSource ≤ D.point minimum := by
    rw [← D.rawCopyData_point_old nonempty proper copy hlast hm hp minimum (by omega)]
    exact copied.point_increasing.monotoneOn (by change nextSource ≤ b.length + 1; omega)
      (by change minimum ≤ b.length + 1; omega) screened
  exact (copied.mark_bound_le_next_source_image r hr markProper nextAt h).trans
    ((copied.toFiniteTraceRows.toInternalTraceRows.actions.action r.val).monotone points)

end IBLP.FiniteBoundedData
