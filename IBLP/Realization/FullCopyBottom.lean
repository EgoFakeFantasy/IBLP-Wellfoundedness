import IBLP.Realization.FullCopyMarkTrace
import IBLP.TraceBounds
import IBLP.MarkTraceSpec
import IBLP.Realization.MarkedRealization

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

include R in
/-- The original filter's p ≤ bottom condition, applied to the actual old
mark trace, supplies the full-copy case without an auxiliary factor-list
location assumption. The paired source is allowed to lie below p. -/
theorem fullCopy_trace_from_bottom (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r mark imageMark bottom : Nat} {trace : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (rowCopy : IBLP.copyRow a last r = some copied)
    (marked : mark ∈ row.marks) (computed : IBLP.markTrace a r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) (full : p ≤ bottom)
    (markImage : IBLP.copyEntry a.length last mark = some imageMark) :
    ∃ source imageTarget, row.columns[row.columns.idxOf mark - row.step]? = some source ∧
      IBLP.copyEntry a.length last source = some imageTarget ∧
      copied.columns[copied.columns.idxOf imageMark - copied.step]? = some imageTarget ∧
      IBLP.markTrace b (r + (a.length - p)) imageMark =
        some (trace.dropLast.map (· + (a.length - p)) ++ [imageTarget]) := by
  obtain ⟨source, history, paired, historyAt, factors, _⟩ := R.marks r row mark hr marked
  have same : history = trace := Option.some.inj (historyAt.symm.trans computed)
  subst history
  have historyShape := (IBLP.markTrace_spec hr paired computed).2.2.unique factors.toTrace
  have bottom : IBLP.fromRight (trace.dropLast ++ [source]) 2 = some bottom := by
    rw [← historyShape]
    exact bottomAt
  have tail := factors.tail_of_bottom bottom full
  have proper := R.proper row (rowAt_mem hr) mark marked
  have markLess := IBLP.Row.properMark_lt (R.data.valid _ _ hr) proper
  have markTail := tail mark factors.start_mem
  obtain ⟨imageTarget, targetImage, newPaired, newTrace⟩ :=
    R.data.fullCopy_markTrace nonempty copy hlast hm hp hr (by omega) rowCopy
      proper markImage paired factors tail
  exact ⟨source, imageTarget, paired, targetImage, newPaired, newTrace⟩

end IBLP.MarkedRealization
