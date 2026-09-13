import IBLP.Realization.CrossingMarkSplit
import IBLP.Realization.CopyPrefix
import IBLP.Realization.CopiedMarkTrace
import IBLP.Realization.ControlMarkTrace
import IBLP.HighFilter

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

include R in
/-- The actual high filter supplies the existing control mark and fixes
the paired source. The program then computes exactly the three-piece chain. -/
theorem highCopy_markTrace (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r mark imageMark bottom boundary imageBoundary : Nat}
    {trace : List Nat} (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (carrierTail : p ≤ r) (rowCopy : IBLP.copyRow a last r = some copied)
    (marked : mark ∈ row.marks) (computed : IBLP.markTrace a r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) (crossing : bottom < p)
    (found : trace.find? (· < p) = some boundary) (high : minimum ≤ boundary)
    (boundaryImage : IBLP.copyEntry a.length last boundary = some imageBoundary)
    (markImage : IBLP.copyEntry a.length last mark = some imageMark)
    (kept : IBLP.keepCopiedMark a last r row copied.columns mark = true) :
    ∃ source front suffix bridge, trace.dropLast = front ++ suffix ∧
      IBLP.markTrace a a.length imageBoundary = some bridge ∧
      copied.columns[copied.columns.idxOf imageMark - copied.step]? = some source ∧
      IBLP.markTrace b (r + (a.length - p)) imageMark =
        some ((front.map (· + (a.length - p)) ++ (bridge.dropLast ++ suffix)) ++ [source]) ∧
      FactorTrace b source imageMark (front.map (· + (a.length - p)) ++ (bridge.dropLast ++ suffix)) := by
  obtain ⟨source, front, suffix, paired, split, before, after, tail, below⟩ :=
    R.crossing_mark_split hr marked computed bottomAt crossing found
  have lastAt := IBLP.getLast_rowAt hlast
  obtain ⟨mapped, sorted, _⟩ := R.data.copyRow_columns nonempty lastAt hm hp hr rowCopy
  have proper := R.proper row (rowAt_mem hr) mark marked
  obtain ⟨controlMarked, sourceLow, _⟩ := IBLP.keepCopiedMark_high_spec
    (R.data.valid _ _ lastAt) (R.data.shapes last (rowAt_mem lastAt)) (R.data.valid _ _ hr) proper
    mapped sorted hm hp computed bottomAt crossing found high boundaryImage markImage paired kept
  obtain ⟨bridge, bridgeAt, bridgeOld, control, _⟩ :=
    R.control_mark_trace hlast hm hp high below boundaryImage controlMarked
  obtain ⟨actualMark, actualImage, factors⟩ :=
    R.data.rawCopy_highTrace nonempty copy hlast hm hp before after tail boundaryImage control bridgeOld
  have same : actualMark = imageMark := Option.some.inj (actualImage.symm.trans markImage)
  subst actualMark
  have sourceImage : IBLP.copyEntry a.length last source = some source := by simp [IBLP.copyEntry, hm, hp, sourceLow]
  obtain ⟨newPaired, newTrace⟩ := R.data.copied_markTrace nonempty copy hlast hm hp hr carrierTail rowCopy
    proper markImage paired sourceImage factors
  exact ⟨source, front, suffix, bridge, split, bridgeAt, newPaired, newTrace, factors⟩

end IBLP.MarkedRealization
