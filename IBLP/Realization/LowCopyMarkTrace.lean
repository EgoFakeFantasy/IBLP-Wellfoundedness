import IBLP.Realization.CrossingMarkSplit
import IBLP.Realization.CopyPrefix
import IBLP.Realization.CopiedMarkTrace

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

include R in
theorem lowCopy_markTrace (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r mark imageMark bottom boundary : Nat} {trace : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (carrierTail : p ≤ r) (rowCopy : IBLP.copyRow a last r = some copied)
    (marked : mark ∈ row.marks) (computed : IBLP.markTrace a r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) (crossing : bottom < p)
    (found : trace.find? (· < p) = some boundary) (low : boundary < minimum)
    (markImage : IBLP.copyEntry a.length last mark = some imageMark) :
    ∃ source front suffix, trace.dropLast = front ++ suffix ∧
      copied.columns[copied.columns.idxOf imageMark - copied.step]? = some source ∧
      IBLP.markTrace b (r + (a.length - p)) imageMark =
        some ((front.map (· + (a.length - p)) ++ suffix) ++ [source]) ∧
      FactorTrace b source imageMark (front.map (· + (a.length - p)) ++ suffix) := by
  obtain ⟨source, front, suffix, paired, split, before, after, tail, below⟩ :=
    R.crossing_mark_split hr marked computed bottomAt crossing found
  have pn : p ≤ a.length := carrierTail.trans (rowAt_le_length hr)
  obtain ⟨actualMark, actualImage, factors⟩ :=
    R.data.rawCopy_lowTrace nonempty copy hlast hm hp before after tail low (by omega)
  have same : actualMark = imageMark := Option.some.inj (actualImage.symm.trans markImage)
  subst actualMark
  have sourceLow := after.target_lt.trans low
  have sourceImage : IBLP.copyEntry a.length last source = some source := by simp [IBLP.copyEntry, hm, hp, sourceLow]
  obtain ⟨newPaired, newTrace⟩ := R.data.copied_markTrace nonempty copy hlast hm hp hr carrierTail rowCopy
    (R.proper row (rowAt_mem hr) mark marked) markImage paired sourceImage factors
  exact ⟨source, front, suffix, split, newPaired, newTrace, factors⟩

end IBLP.MarkedRealization
