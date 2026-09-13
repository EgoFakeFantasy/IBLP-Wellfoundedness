import IBLP.Realization.ActionGraphCongruence
import IBLP.Realization.FullCopyWeak
import IBLP.Realization.RetainedMark
import IBLP.Extender.CriticalAction

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem rawCopy_rowAction_image (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p : Nat} (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (r : FiniteRowIndex a) (s : FiniteRowIndex b) (tail : p ≤ r.val)
    (owner : s.val = r.val + (a.length - p)) :
    CutAction.Image (D.lastExtension nonempty).embedding (stage.ordinalImage (D.lastExtension nonempty).embedding)
      (D.toFiniteTraceRows.toInternalTraceRows.actions.action r.val)
      ((D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows.actions.action s.val) := by
  let image := D.image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding
  let copied := D.rawCopyData nonempty proper copy hlast hm hp
  have graphs : image.graph r = copied.graph s :=
    (D.rawCopyData_graph_new nonempty proper copy hlast hm hp s r (by have := r.property.2; omega) owner).symm
  rw [← image.rowAction_congr_graphs copied r s graphs]
  exact D.rowAction_image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding r

theorem rawCopy_traceAction_image (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start target' start' : Nat} {rows : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (h : FactorTrace a target start rows)
    (h' : FactorTrace b target' start' (rows.map (· + (a.length - p)))) (tail : ∀ r ∈ rows, p ≤ r) :
    CutAction.Image (D.lastExtension nonempty).embedding (stage.ordinalImage (D.lastExtension nonempty).embedding)
      (h.word D.toFiniteTraceRows.toInternalTraceRows.actions)
      (h'.word (D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows.actions) := by
  let image := D.image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding
  let copied := D.rawCopyData nonempty proper copy hlast hm hp
  have graphs : image.traceGraph h = copied.traceGraph h' :=
    (D.traceGraph_image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding h).trans
      (D.fullCopy_traceGraph nonempty proper copy hlast hm hp h h' tail).symm
  rw [← image.traceAction_congr_graphs copied h h' graphs]
  exact D.traceAction_image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding h

theorem rawCopy_traceAction_old (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start : Nat} {rows : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (h : FactorTrace a target start rows) (old : start < a.length) (z : (D.lastExtension nonempty).next.model.Element) :
    ((h.word D.toFiniteTraceRows.toInternalTraceRows.actions).act ((D.lastExtension nonempty).toSource z)).val =
      (((IBLP.rawCopy_factorTrace_old copy h old).word
        (D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows.actions).act z).val :=
  D.traceAction_congr_values (D.rawCopyData nonempty proper copy hlast hm hp) h
    (IBLP.rawCopy_factorTrace_old copy h old) (D.rawCopy_traceGraph_old nonempty proper copy hlast hm hp h old)
    ((D.lastExtension nonempty).toSource z) z rfl

theorem rawCopy_traceBounds_old (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start : Nat} {rows : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (h : FactorTrace a target start rows) (old : start < a.length) :
    (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound =
      ((IBLP.rawCopy_factorTrace_old copy h old).word
        (D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows.actions).bound :=
  ((D.traceGraph_elementary h).bounds_absolute
    ((D.rawCopyData nonempty proper copy hlast hm hp).traceGraph_elementary (IBLP.rawCopy_factorTrace_old copy h old))
    (D.rawCopy_traceGraph_old nonempty proper copy hlast hm hp h old)).2

end IBLP.FiniteBoundedData
