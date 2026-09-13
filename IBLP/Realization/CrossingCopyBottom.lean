import IBLP.Realization.LowCopyMarkTrace
import IBLP.Realization.HighCopyMarkTrace
import IBLP.TraceBottom

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

include R in
/-- Low crossing preserves the actual old bottom factor, not merely the
existence of a new accurate trace. -/
theorem lowCopy_bottom (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r mark imageMark bottom boundary : Nat} {trace : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (carrierTail : p ≤ r) (rowCopy : IBLP.copyRow a last r = some copied)
    (marked : mark ∈ row.marks) (computed : IBLP.markTrace a r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) (crossing : bottom < p)
    (found : trace.find? (· < p) = some boundary) (low : boundary < minimum)
    (markImage : IBLP.copyEntry a.length last mark = some imageMark) :
    ∃ newTrace, IBLP.markTrace b (r + (a.length - p)) imageMark = some newTrace ∧
      IBLP.fromRight newTrace 2 = some bottom := by
  obtain ⟨source, front, suffix, paired, split, before, after, tail, below⟩ :=
    R.crossing_mark_split hr marked computed bottomAt crossing found
  have pn := carrierTail.trans (rowAt_le_length hr)
  obtain ⟨actualMark, actualImage, factors⟩ :=
    R.data.rawCopy_lowTrace nonempty copy hlast hm hp before after tail low (by omega)
  have same : actualMark = imageMark := Option.some.inj (actualImage.symm.trans markImage)
  subst actualMark
  have sourceLow := after.target_lt.trans low
  have sourceImage : IBLP.copyEntry a.length last source = some source := by
    simp [IBLP.copyEntry, hm, hp, sourceLow]
  obtain ⟨_, newTrace⟩ := R.data.copied_markTrace nonempty copy hlast hm hp hr carrierTail rowCopy
    (R.proper row (rowAt_mem hr) mark marked) markImage paired sourceImage factors
  have oldShape := (IBLP.markTrace_spec hr paired computed).2.2.unique (before.appendTrace after).toTrace
  refine ⟨_, newTrace, ?_⟩
  exact IBLP.fromRight_two_same_suffix after.nonempty (by rw [← oldShape]; exact bottomAt)

include R in
/-- The additional high-crossing bridge precedes a nonempty original suffix,
so the actual old bottom factor is preserved as well. -/
theorem highCopy_bottom (nonempty : 0 < a.length) {b : IBLP.Pattern}
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
    ∃ newTrace, IBLP.markTrace b (r + (a.length - p)) imageMark = some newTrace ∧
      IBLP.fromRight newTrace 2 = some bottom := by
  obtain ⟨source, front, suffix, paired, split, before, after, tail, below⟩ :=
    R.crossing_mark_split hr marked computed bottomAt crossing found
  have lastAt := IBLP.getLast_rowAt hlast
  obtain ⟨mapped, sorted, _⟩ := R.data.copyRow_columns nonempty lastAt hm hp hr rowCopy
  have proper := R.proper row (rowAt_mem hr) mark marked
  obtain ⟨controlMarked, sourceLow, _⟩ := IBLP.keepCopiedMark_high_spec
    (R.data.valid _ _ lastAt) (R.data.shapes last (rowAt_mem lastAt)) (R.data.valid _ _ hr) proper
    mapped sorted hm hp computed bottomAt crossing found high boundaryImage markImage paired kept
  obtain ⟨bridge, _, bridgeOld, control, _⟩ :=
    R.control_mark_trace hlast hm hp high below boundaryImage controlMarked
  obtain ⟨actualMark, actualImage, factors⟩ :=
    R.data.rawCopy_highTrace nonempty copy hlast hm hp before after tail boundaryImage control bridgeOld
  have same : actualMark = imageMark := Option.some.inj (actualImage.symm.trans markImage)
  subst actualMark
  have sourceImage : IBLP.copyEntry a.length last source = some source := by
    simp [IBLP.copyEntry, hm, hp, sourceLow]
  obtain ⟨_, newTrace⟩ := R.data.copied_markTrace nonempty copy hlast hm hp hr carrierTail rowCopy
    proper markImage paired sourceImage factors
  have oldShape := (IBLP.markTrace_spec hr paired computed).2.2.unique (before.appendTrace after).toTrace
  refine ⟨_, newTrace, ?_⟩
  rw [← List.append_assoc]
  exact IBLP.fromRight_two_same_suffix after.nonempty (by rw [← oldShape]; exact bottomAt)

end IBLP.MarkedRealization
