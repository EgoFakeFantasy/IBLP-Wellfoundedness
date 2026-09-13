import IBLP.Realization.FullCopyWeak
import IBLP.Realization.FullCopyMark

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- The literal full-copy branch preserves the actual mark together with
its accurate trace and weak equality on the whole new natural bound. -/
theorem fullCopy_markRealized (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r mark bottom : Nat} {trace : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (rowCopy : IBLP.copyRow a last r = some copied)
    (marked : mark ∈ row.marks) (computed : IBLP.markTrace a r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) (full : p ≤ bottom) :
    ∃ imageMark, IBLP.copyEntry a.length last mark = some imageMark ∧ imageMark ∈ copied.marks ∧
      (R.data.rawCopyData nonempty R.proper copy hlast hm hp).MarkRealized
        (r + (a.length - p)) copied imageMark := by
  obtain ⟨imageMark, source, imageTarget, markImage, newMarked, paired, targetImage, newPaired, newTrace⟩ :=
    R.fullCopy_mark nonempty copy hlast hm hp hr rowCopy marked computed bottomAt full
  obtain ⟨oldSource, history, oldPaired, historyAt, factors, certificate⟩ := R.marks r row mark hr marked
  have sameSource : oldSource = source := Option.some.inj (oldPaired.symm.trans paired)
  subst oldSource
  have sameHistory : history = trace := Option.some.inj (historyAt.symm.trans computed)
  subst history
  have historyShape := (IBLP.markTrace_spec hr paired computed).2.2.unique factors.toTrace
  have bottom : IBLP.fromRight (trace.dropLast ++ [source]) 2 = some bottom := by
    rw [← historyShape]
    exact bottomAt
  have tail := factors.tail_of_bottom bottom full
  have markTail := tail mark factors.start_mem
  have markLess := IBLP.Row.properMark_lt (R.data.valid _ _ hr) (R.proper row (rowAt_mem hr) mark marked)
  have carrierTail : p ≤ r := by omega
  have translated := IBLP.copyEntry_tail (R.data.valid _ _ (IBLP.getLast_rowAt hlast)) hm hp markTail
  have sameMark : imageMark = mark + (a.length - p) := Option.some.inj (markImage.symm.trans translated)
  obtain ⟨actual, atActual, actualCopy⟩ := IBLP.rawCopy_row_image copy hlast hp carrierTail (rowAt_le_length hr)
  have sameRow : actual = copied := Option.some.inj (actualCopy.symm.trans rowCopy)
  subst actual
  obtain ⟨otherTarget, otherImage, newFactors⟩ :=
    R.data.rawCopy_factorTrace nonempty copy hlast hm hp factors tail
  have sameTarget : otherTarget = imageTarget := Option.some.inj (otherImage.symm.trans targetImage)
  subst otherTarget
  have actualFactors : FactorTrace b imageTarget imageMark (trace.dropLast.map (· + (a.length - p))) :=
    sameMark.symm ▸ newFactors
  let oldIndex : FiniteRowIndex a := ⟨r, rowAt_pos hr, rowAt_le_length hr⟩
  let newIndex : FiniteRowIndex b := ⟨r + (a.length - p), rowAt_pos atActual, rowAt_le_length atActual⟩
  have newCertificate := (R.data.fullCopy_markCertificate nonempty R.proper copy hlast hm hp
    oldIndex newIndex carrierTail rfl factors actualFactors tail).mpr certificate
  refine ⟨imageMark, markImage, newMarked, imageTarget,
    trace.dropLast.map (· + (a.length - p)) ++ [imageTarget], newPaired, newTrace, ?_⟩
  simpa only [List.dropLast_concat] using ⟨actualFactors, newCertificate⟩

end IBLP.MarkedRealization
