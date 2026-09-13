import IBLP.Realization.CrossingCopyBottom
import IBLP.Realization.FullCopyBottom
import IBLP.CopyMarkCases
import IBLP.CopyMarks

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

include R in
theorem fullCopy_bottom (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r mark imageMark bottom : Nat} {trace : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (rowCopy : IBLP.copyRow a last r = some copied)
    (marked : mark ∈ row.marks) (computed : IBLP.markTrace a r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) (full : p ≤ bottom)
    (markImage : IBLP.copyEntry a.length last mark = some imageMark) :
    ∃ newTrace, IBLP.markTrace b (r + (a.length - p)) imageMark = some newTrace ∧
      IBLP.fromRight newTrace 2 = some (bottom + (a.length - p)) := by
  obtain ⟨source, imageTarget, _, _, _, newTrace⟩ :=
    R.fullCopy_trace_from_bottom nonempty copy hlast hm hp hr rowCopy marked computed bottomAt full markImage
  have atLast : trace.dropLast.getLast? = some bottom := by
    rw [← IBLP.fromRight_two_dropLast]
    exact bottomAt
  have factorsNonempty : trace.dropLast ≠ [] := by intro empty; simp [empty] at atLast
  have mappedNonempty : trace.dropLast.map (· + (a.length - p)) ≠ [] := by
    intro empty
    have length := congrArg List.length empty
    simp only [List.length_map, List.length_nil] at length
    exact factorsNonempty (List.length_eq_zero_iff.mp length)
  refine ⟨_, newTrace, (IBLP.fromRight_two_append mappedNonempty imageTarget _).mpr ?_⟩
  simp only [List.getLast?_map, atLast, Option.map_some]

include R in
/-- Exact bottom transition for every mark accepted by the original filter.
Full copies translate the bottom; both crossing branches retain it. -/
theorem copied_bottom (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r mark imageMark bottom : Nat} {trace : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (carrierTail : p ≤ r) (rowCopy : IBLP.copyRow a last r = some copied)
    (marked : mark ∈ row.marks) (computed : IBLP.markTrace a r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom)
    (markImage : IBLP.copyEntry a.length last mark = some imageMark)
    (kept : IBLP.keepCopiedMark a last r row copied.columns mark = true) :
    ∃ newTrace, IBLP.markTrace b (r + (a.length - p)) imageMark = some newTrace ∧
      IBLP.fromRight newTrace 2 = some (if p ≤ bottom then bottom + (a.length - p) else bottom) := by
  by_cases full : p ≤ bottom
  · simpa only [if_pos full] using
      R.fullCopy_bottom nonempty copy hlast hm hp hr rowCopy marked computed bottomAt full markImage
  · obtain ⟨oldTrace, oldBottom, oldComputed, oldAt, branch⟩ := IBLP.keepCopiedMark_cases hm hp kept
    have sameTrace : oldTrace = trace := Option.some.inj (oldComputed.symm.trans computed)
    subst oldTrace
    have sameBottom : oldBottom = bottom := Option.some.inj (oldAt.symm.trans bottomAt)
    subst oldBottom
    rcases branch with impossible | ⟨crossing, boundary, found, low | ⟨high, imageBoundary, boundaryImage⟩⟩
    · exact False.elim (full impossible)
    · simpa only [if_neg full] using
        R.lowCopy_bottom nonempty copy hlast hm hp hr carrierTail rowCopy marked computed bottomAt crossing found low markImage
    · simpa only [if_neg full] using
        R.highCopy_bottom nonempty copy hlast hm hp hr carrierTail rowCopy marked computed bottomAt
          crossing found high boundaryImage markImage kept

include R in
/-- Recover an old mark and its exact bottom transition from an actual stored
copied mark. Canonicalized mark lists introduce no additional origins. -/
theorem copied_mark_bottom_origin (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r imageMark : Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (carrierTail : p ≤ r) (rowCopy : IBLP.copyRow a last r = some copied)
    (marked : imageMark ∈ copied.marks) :
    ∃ mark trace bottom newTrace, mark ∈ row.marks ∧
      IBLP.copyEntry a.length last mark = some imageMark ∧
      IBLP.markTrace a r mark = some trace ∧ IBLP.fromRight trace 2 = some bottom ∧
      IBLP.markTrace b (r + (a.length - p)) imageMark = some newTrace ∧
      IBLP.fromRight newTrace 2 = some (if p ≤ bottom then bottom + (a.length - p) else bottom) := by
  obtain ⟨mark, oldMarked, _, kept, markImage⟩ := FiniteBoundedData.copyRow_mark_origin hr rowCopy marked
  obtain ⟨trace, bottom, computed, bottomAt, _⟩ := IBLP.keepCopiedMark_cases hm hp kept
  obtain ⟨newTrace, newComputed, newBottom⟩ :=
    R.copied_bottom nonempty copy hlast hm hp hr carrierTail rowCopy oldMarked computed bottomAt markImage kept
  exact ⟨mark, trace, bottom, newTrace, oldMarked, markImage, computed, bottomAt, newComputed, newBottom⟩

end IBLP.MarkedRealization
