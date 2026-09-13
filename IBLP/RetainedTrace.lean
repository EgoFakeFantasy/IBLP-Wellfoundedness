import IBLP.RawCopy
import IBLP.Realization.TraceWord
import IBLP.MarkTraceSpec

namespace IBLP

theorem rawCopy_predecessor_old {a b : Pattern} {r : Nat}
    (copy : rawCopy a = some b) (old : r < a.length) : predecessor b r = predecessor a r := by
  unfold predecessor
  rw [rawCopy_prefix copy old]

theorem rawCopy_factorTrace_old {a b : Pattern} {target start : Nat} {rows : List Nat}
    (copy : rawCopy a = some b) (h : FactorTrace a target start rows) (old : start < a.length) :
    FactorTrace b target start rows := by
  induction h with
  | single hp hn => exact .single ((rawCopy_predecessor_old copy old).trans hp) hn
  | cons hp hn inner ih =>
    exact .cons ((rawCopy_predecessor_old copy old).trans hp) hn (ih (by omega))

theorem rawCopy_trace_old {a b : Pattern} {target start : Nat} {rows : List Nat}
    (copy : rawCopy a = some b) (h : Trace a target start rows) (old : start < a.length) :
    Trace b target start rows := by
  induction h with
  | done => exact .done
  | step ht hp hn inner ih =>
    exact .step ht ((rawCopy_predecessor_old copy old).trans hp) hn (ih (by omega))

theorem rawCopy_markTrace_old {a b : Pattern} {r mark source : Nat} {row : Row} {trace : List Nat}
    (copy : rawCopy a = some b) (old : r < a.length) (hr : rowAt a r = some row)
    (below : mark < r) (paired : row.columns[row.columns.idxOf mark - row.step]? = some source)
    (computed : markTrace a r mark = some trace) : markTrace b r mark = some trace := by
  obtain ⟨member, index, history⟩ := markTrace_spec hr paired computed
  have history' := rawCopy_trace_old copy history (by omega)
  have newRow := (rawCopy_prefix copy old).trans hr
  simp [markTrace, newRow, member, index, paired, traceFrom_iff.mpr history']

end IBLP
