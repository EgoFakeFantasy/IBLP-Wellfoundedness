import IBLP.Realization.NativeWordRestriction
import IBLP.Realization.NativePrefixMarks
import IBLP.NativeSuffixTrace

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- Every actual suffix mark keeps its paired source and accurate shifted
history. The new word and carrier use their actual restrictions, so the
certificate holds on the new whole natural bound. -/
theorem native_suffix_markRealized (r : FiniteRowIndex a) {baseRow oldRow : IBLP.Row} {p e i mark : Nat}
    {sources : List Nat} {b : IBLP.Pattern}
    (hr : IBLP.rowAt a r.val = some baseRow) (hp : baseRow.p = some p) (he : baseRow.e = some e)
    (sourcesRun : IBLP.nativeSources a r.val = some sources) (run : IBLP.native a r.val = some (b, sources))
    (atOld : IBLP.rowAt a i = some oldRow) (after : r.val < i) (marked : mark ∈ oldRow.marks) :
    (R.data.nativeData r hr hp he sourcesRun R.proper run).MarkRealized (i + sources.length)
      (oldRow.shiftAfter r.val sources.length) (IBLP.shiftAfter r.val sources.length mark) := by
  obtain ⟨source, trace, paired, _, factors, certificate⟩ := R.marks i oldRow mark atOld marked
  have markProper := R.proper oldRow (rowAt_mem atOld) mark marked
  have below := IBLP.Row.properMark_lt (R.data.valid _ _ atOld) markProper
  have atNew : IBLP.rowAt b (i + sources.length) = some (oldRow.shiftAfter r.val sources.length) := by
    rw [IBLP.native_suffix_rowAt run after, atOld]; rfl
  let oldIndex : FiniteRowIndex a := ⟨i, rowAt_pos atOld, rowAt_le_length atOld⟩
  let newIndex : FiniteRowIndex b := ⟨i + sources.length, rowAt_pos atNew, rowAt_le_length atNew⟩
  have owner : newIndex.val = IBLP.shiftAfter r.val sources.length oldIndex.val := by
    simp only [newIndex, oldIndex, IBLP.shiftAfter, if_pos after]
  have newCertificate := R.data.native_shift_markCertificate r hr hp he sourcesRun R.proper run
    oldIndex newIndex owner factors below certificate
  refine ⟨IBLP.shiftAfter r.val sources.length source,
    trace.dropLast.map (IBLP.shiftAfter r.val sources.length) ++ [IBLP.shiftAfter r.val sources.length source],
    IBLP.native_suffix_pair R.data.valid R.data.shapes R.proper run atOld after markProper paired,
    IBLP.native_suffix_markTrace R.data.valid R.data.shapes R.proper run atOld after markProper paired factors, ?_⟩
  simp only [List.dropLast_concat]
  exact ⟨factors.native_shift R.data.valid R.data.shapes run, newCertificate⟩

end IBLP.MarkedRealization
