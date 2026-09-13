import IBLP.Realization.HighCopyWeak
import IBLP.Realization.HighInputBound
import IBLP.Realization.HighCopyMarkTrace
import IBLP.CopyMarks

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- The literal high-crossing branch, including its next-source screen,
preserves the actual mark and its complete certificate at the computed
natural bound. All three high-transfer bounds are discharged from arrays
and the existing control mark. -/
theorem highCopy_markRealized (nonempty : 0 < a.length) {b : IBLP.Pattern}
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
    imageMark ∈ copied.marks ∧
      (R.data.rawCopyData nonempty R.proper copy hlast hm hp).MarkRealized
        (r + (a.length - p)) copied imageMark := by
  have lastAt := IBLP.getLast_rowAt hlast
  have column := (R.data.valid _ _ hr).2.2.2 mark marked
  have newMarked := IBLP.copyRow_kept_mark hr rowCopy marked column kept markImage
  have proper := R.proper row (rowAt_mem hr) mark marked
  obtain ⟨mapped, sorted, step⟩ := R.data.copyRow_columns nonempty lastAt hm hp hr rowCopy
  obtain ⟨source, front, suffix, paired, split, before, after, tail, below⟩ :=
    R.crossing_mark_split hr marked computed bottomAt crossing found
  obtain ⟨controlMarked, sourceLow, nextSource, imageNext, nextAt, nextImage, nextBound, _⟩ :=
    IBLP.keepCopiedMark_high_spec (R.data.valid _ _ lastAt) (R.data.shapes last (rowAt_mem lastAt))
      (R.data.valid _ _ hr) proper mapped sorted hm hp computed bottomAt crossing found high boundaryImage markImage paired kept
  have newNextAt := IBLP.copied_next_source_index (R.data.valid _ _ hr) proper mapped sorted step markImage nextAt nextImage
  obtain ⟨bridge, _, old, control, controlCertificate⟩ :=
    R.control_mark_trace hlast hm hp high below boundaryImage controlMarked
  obtain ⟨actualMark, actualImage, newBefore⟩ :=
    R.data.rawCopy_factorPrefix nonempty copy hlast hm hp before tail boundaryImage
  have sameMark : actualMark = imageMark := Option.some.inj (actualImage.symm.trans markImage)
  subst actualMark
  let factors := newBefore.appendTrace ((IBLP.rawCopy_factorTrace_old copy control old).append
    (IBLP.rawCopy_factorTrace_old copy after (control.target_lt.trans old)))
  have sourceImage : IBLP.copyEntry a.length last source = some source := by simp [IBLP.copyEntry, hm, hp, sourceLow]
  obtain ⟨newPaired, newTrace⟩ := R.data.copied_markTrace nonempty copy hlast hm hp hr carrierTail rowCopy
    proper markImage paired sourceImage factors
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
  have newProper := R.data.copyRow_proper nonempty lastAt hm hp hr (R.proper row (rowAt_mem hr)) rowCopy imageMark newMarked
  have newCertificate := R.data.highCopy_markCertificate nonempty R.proper copy hlast hm hp
    oldIndex newIndex carrierTail rfl before after tail control old newBefore oldCertificate controlCertificate
    (fun h => R.data.highCopy_input_bound nonempty R.proper copy hlast hm hp newIndex atActual newProper newNextAt nextBound h)
  refine ⟨newMarked, source, (front.map (· + (a.length - p)) ++ (bridge.dropLast ++ suffix)) ++ [source],
    newPaired, newTrace, ?_⟩
  simpa only [List.dropLast_concat] using ⟨factors, newCertificate⟩

end IBLP.MarkedRealization
