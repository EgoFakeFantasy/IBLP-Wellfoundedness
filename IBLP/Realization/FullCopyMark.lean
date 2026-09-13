import IBLP.Realization.FullCopyBottom
import IBLP.CopyMarks

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

include R in
/-- The original full-copy filter really retains the mark, and the new
algorithm computes its complete accurate trace with the paired-source image. -/
theorem fullCopy_mark (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r mark bottom : Nat} {trace : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (rowCopy : IBLP.copyRow a last r = some copied)
    (marked : mark ∈ row.marks) (computed : IBLP.markTrace a r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) (full : p ≤ bottom) :
    ∃ imageMark source imageTarget,
      IBLP.copyEntry a.length last mark = some imageMark ∧ imageMark ∈ copied.marks ∧
      row.columns[row.columns.idxOf mark - row.step]? = some source ∧
      IBLP.copyEntry a.length last source = some imageTarget ∧
      copied.columns[copied.columns.idxOf imageMark - copied.step]? = some imageTarget ∧
      IBLP.markTrace b (r + (a.length - p)) imageMark =
        some (trace.dropLast.map (· + (a.length - p)) ++ [imageTarget]) := by
  have column := (R.data.valid _ _ hr).2.2.2 mark marked
  have mapped := (R.data.copyRow_columns nonempty (IBLP.getLast_rowAt hlast) hm hp hr rowCopy).1
  obtain ⟨imageMark, _, image⟩ := IBLP.mapped_mem_left mapped column
  have kept := IBLP.keepCopiedMark_full (row := row) (cols := copied.columns) hm hp computed bottomAt full
  have newMarked := IBLP.copyRow_kept_mark hr rowCopy marked column kept image
  obtain ⟨source, imageTarget, paired, targetImage, newPaired, newTrace⟩ :=
    R.fullCopy_trace_from_bottom nonempty copy hlast hm hp hr rowCopy marked computed bottomAt full image
  exact ⟨imageMark, source, imageTarget, image, newMarked, paired, targetImage, newPaired, newTrace⟩

end IBLP.MarkedRealization
