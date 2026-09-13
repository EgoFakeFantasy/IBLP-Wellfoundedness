import IBLP.Realization.CopyActions
import IBLP.Extender.LowImageAgreement

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem criticalPoint_le_source (r : FiniteRowIndex a) {row : IBLP.Row} {minimum : Nat}
    (hr : rowAt a r.val = some row) (hm : row.columns.head? = some minimum) : D.point minimum ≤ D.source r.val := by
  obtain ⟨y, edge, _⟩ := (D.critical r row minimum hr hm).2.1
  have dom := (ZFSet.pair_mem_prod.mp ((D.graph_represents r).1.1
    ((stage.model.graphApplies_absolute _ _ _).mp edge))).1
  exact Order.le_of_lt_succ ((stage.ordinal_mem_hierarchy _ _).mp dom)

theorem traceBound_le_point {target start boundary : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) (below : start < boundary) (inside : boundary ≤ a.length + 1) :
    (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound ≤ D.point boundary :=
  (h.bound_interval D.toFiniteTraceRows.toInternalTraceRows.actions).2.trans
    (D.point_increasing.monotoneOn (by change start + 1 ≤ a.length + 1; omega)
      (by change boundary ≤ a.length + 1; exact inside) (by omega))

theorem lowSuffix_allInputs (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start : Nat} {rows : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (h : FactorTrace a target start rows) (low : start < minimum) (old : start < a.length) :
    CutAction.AllInputAgreement
      (h.word (D.image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding).toFiniteTraceRows.toInternalTraceRows.actions)
      ((IBLP.rawCopy_factorTrace_old copy h old).word
        (D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows.actions)
      (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound := by
  have lastAt := IBLP.getLast_rowAt hlast
  have mp := IBLP.Row.minimum_le_column (D.valid _ _ lastAt) hm (IBLP.fromRight_mem hp)
  have pn := IBLP.fromRight_le_last (D.valid _ _ lastAt).1 (D.valid _ _ lastAt).2.2.1 (by omega) hp
  exact (D.lastExtension nonempty).low_image_allInputs (D.point minimum)
    (D.criticalPoint_le_source (lastIndex nonempty) lastAt hm)
    (D.critical (lastIndex nonempty) last minimum lastAt hm)
    (D.traceAction_image (D.lastExtension nonempty).next (D.lastExtension nonempty).embedding h)
    (D.rawCopy_traceAction_old nonempty proper copy hlast hm hp h old)
    (D.traceBound_le_point h low (by omega))

end IBLP.FiniteBoundedData
