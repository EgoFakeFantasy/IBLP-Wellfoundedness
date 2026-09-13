import IBLP.Realization.LowCopyWeak
import IBLP.Realization.LowCopyMarkTrace
import IBLP.CopyMarks

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- The original low-crossing filter preserves the actual copied mark,
its computed accurate trace, and weak equality on the entire new natural
bound, including the empty-front and critical-boundary cases. -/
theorem lowCopy_markRealized (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r mark bottom boundary : Nat} {trace : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (carrierTail : p ≤ r) (rowCopy : IBLP.copyRow a last r = some copied)
    (marked : mark ∈ row.marks) (computed : IBLP.markTrace a r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) (crossing : bottom < p)
    (found : trace.find? (· < p) = some boundary) (low : boundary < minimum) :
    ∃ imageMark, IBLP.copyEntry a.length last mark = some imageMark ∧ imageMark ∈ copied.marks ∧
      (R.data.rawCopyData nonempty R.proper copy hlast hm hp).MarkRealized
        (r + (a.length - p)) copied imageMark := by
  have column := (R.data.valid _ _ hr).2.2.2 mark marked
  have mapped := (R.data.copyRow_columns nonempty (IBLP.getLast_rowAt hlast) hm hp hr rowCopy).1
  obtain ⟨imageMark, _, markImage⟩ := IBLP.mapped_mem_left mapped column
  have kept : IBLP.keepCopiedMark a last r row copied.columns mark = true := by
    simp [IBLP.keepCopiedMark, hm, hp, computed, bottomAt, show ¬p ≤ bottom by omega, found, low]
  have newMarked := IBLP.copyRow_kept_mark hr rowCopy marked column kept markImage
  obtain ⟨source, front, suffix, paired, split, before, after, tail, below⟩ :=
    R.crossing_mark_split hr marked computed bottomAt crossing found
  have pn := carrierTail.trans (rowAt_le_length hr)
  have old : boundary < a.length := by omega
  have boundaryImage : IBLP.copyEntry a.length last boundary = some boundary := by simp [IBLP.copyEntry, hm, hp, low]
  obtain ⟨actualMark, actualImage, newBefore⟩ :=
    R.data.rawCopy_factorPrefix nonempty copy hlast hm hp before tail boundaryImage
  have sameMark : actualMark = imageMark := Option.some.inj (actualImage.symm.trans markImage)
  subst actualMark
  let factors := newBefore.appendTrace (IBLP.rawCopy_factorTrace_old copy after old)
  have sourceLow := after.target_lt.trans low
  have sourceImage : IBLP.copyEntry a.length last source = some source := by simp [IBLP.copyEntry, hm, hp, sourceLow]
  obtain ⟨newPaired, newTrace⟩ := R.data.copied_markTrace nonempty copy hlast hm hp hr carrierTail rowCopy
    (R.proper row (rowAt_mem hr) mark marked) markImage paired sourceImage factors
  obtain ⟨oldSource, history, oldPaired, historyAt, oldFactors, certificate⟩ := R.marks r row mark hr marked
  have sameSource : oldSource = source := Option.some.inj (oldPaired.symm.trans paired)
  subst oldSource
  have sameHistory : history = trace := Option.some.inj (historyAt.symm.trans computed)
  subst history
  have oldCertificate : (before.appendTrace after).MarkCertificate R.data.toFiniteTraceRows.toInternalTraceRows r := by
    simpa only [split] using certificate
  obtain ⟨actual, atActual, actualCopy⟩ := IBLP.rawCopy_row_image copy hlast hp carrierTail (rowAt_le_length hr)
  have sameRow : actual = copied := Option.some.inj (actualCopy.symm.trans rowCopy)
  subst actual
  let oldIndex : FiniteRowIndex a := ⟨r, rowAt_pos hr, rowAt_le_length hr⟩
  let newIndex : FiniteRowIndex b := ⟨r + (a.length - p), rowAt_pos atActual, rowAt_le_length atActual⟩
  have newCertificate := R.data.lowCopy_markCertificate nonempty R.proper copy hlast hm hp
    oldIndex newIndex carrierTail rfl before after tail low old newBefore oldCertificate
  refine ⟨imageMark, markImage, newMarked, source,
    (front.map (· + (a.length - p)) ++ suffix) ++ [source], newPaired, newTrace, ?_⟩
  simpa only [List.dropLast_concat] using ⟨factors, newCertificate⟩

end IBLP.MarkedRealization
