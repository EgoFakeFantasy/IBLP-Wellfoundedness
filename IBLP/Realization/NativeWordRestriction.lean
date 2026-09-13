import IBLP.Realization.NativeActions
import IBLP.Realization.MarkRestriction
import IBLP.NativeTraceShift

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
  (sourcesRun : IBLP.nativeSources a r.val = some sources) (proper : IBLP.ProperMarks a)
  {b : IBLP.Pattern} (run : IBLP.native a r.val = some (b, sources))

/-- Each factor of a transported old history is replaced by its actual
restriction. Composition therefore gives the whole-word restriction (3.9). -/
theorem native_word_restriction {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) :
    CutRestriction
      ((h.native_shift D.valid D.shapes run).word (D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows.actions)
      (h.word D.toFiniteTraceRows.toInternalTraceRows.actions) := by
  let E := D.nativeData r hr hp he sourcesRun proper run
  have rowRestriction (i q : Nat) (pred : IBLP.predecessor a i = some q) :
      CutRestriction (E.toFiniteTraceRows.toInternalTraceRows.actions.action (IBLP.shiftAfter r.val sources.length i))
        (D.toFiniteTraceRows.toInternalTraceRows.actions.action i) := by
    have oldIndex := predecessor_row_index pred
    have newIndex := predecessor_row_index (IBLP.native_predecessor_shift D.valid D.shapes run pred)
    exact D.nativeData_row_restriction r hr hp he sourcesRun proper run ⟨i, oldIndex⟩
      ⟨IBLP.shiftAfter r.val sources.length i, newIndex⟩ rfl
  induction h with
  | @single start pred less => exact rowRestriction start _ pred
  | @cons start next tail pred less inner ih =>
    change CutRestriction
      (CutAction.listWord E.toFiniteTraceRows.toInternalTraceRows.actions.action
        (IBLP.shiftAfter r.val sources.length start :: tail.map (IBLP.shiftAfter r.val sources.length)) _)
      (CutAction.listWord D.toFiniteTraceRows.toInternalTraceRows.actions.action (start :: tail) _)
    rw [CutAction.listWord_cons _ _ _ (by simpa using inner.nonempty),
      CutAction.listWord_cons _ _ _ inner.nonempty]
    exact (rowRestriction start next pred).comp ih

theorem native_shift_markCertificate (i : FiniteRowIndex a) (j : FiniteRowIndex b)
    (owner : j.val = IBLP.shiftAfter r.val sources.length i.val)
    {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) (before : start < i.val)
    (certificate : h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows i.val) :
    (h.native_shift D.valid D.shapes run).MarkCertificate
      (D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows j.val := by
  apply D.markCertificate_of_restrictions (D.nativeData r hr hp he sourcesRun proper run) i j h
    (h.native_shift D.valid D.shapes run)
  · rw [owner]
    exact IBLP.shiftAfter_strictMono _ _ before
  · exact D.nativeData_row_restriction r hr hp he sourcesRun proper run i j owner
  · exact D.native_word_restriction r hr hp he sourcesRun proper run h
  · exact certificate

end IBLP.FiniteBoundedData
