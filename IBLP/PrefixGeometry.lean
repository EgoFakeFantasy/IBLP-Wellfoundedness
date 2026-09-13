import IBLP.Realization.RowGeometry
import IBLP.MarkTraceSpec

namespace IBLP

theorem rowAt_take {a : Pattern} {k r : Nat} (bound : r ≤ k) : rowAt (a.take k) r = rowAt a r := by
  by_cases zero : r = 0
  · simp [zero, rowAt]
  · simp only [rowAt, zero, ↓reduceIte]
    exact List.getElem?_take_of_lt (by omega)

theorem take_row_origin {a : Pattern} {k r : Nat} {row : Row}
    (hr : rowAt (a.take k) r = some row) : rowAt a r = some row := by
  have bound := rowAt_le_length hr
  rw [List.length_take] at bound
  exact (rowAt_take (by omega : r ≤ k)).symm.trans hr

theorem BasicValid.take {a : Pattern} (valid : BasicValid a) (k : Nat) : BasicValid (a.take k) :=
  fun _ _ hr => valid _ _ (take_row_origin hr)

theorem OrdinaryShape.take {a : Pattern} (shapes : OrdinaryShape a) (k : Nat) : OrdinaryShape (a.take k) :=
  fun row member => shapes row (List.mem_of_mem_take member)

theorem ProperMarks.take {a : Pattern} (proper : ProperMarks a) (k : Nat) : ProperMarks (a.take k) :=
  fun row member => proper row (List.mem_of_mem_take member)

theorem Saturated.take {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    (saturated : Saturated a) (k : Nat) : Saturated (a.take k) := by
  intro r row p e q hr hp he hq
  have old := take_row_origin hr
  have rb := rowAt_le_length hr
  have eb := fromRight_le_last (valid _ _ old).1 (valid _ _ old).2.2.1
    (Row.step_pos (shapes row (rowAt_mem old))) he
  have eq : penultimate (a.take k) e = penultimate a e := by
    unfold penultimate
    rw [rowAt_take (by simp only [List.length_take] at rb; omega : e ≤ k)]
  exact saturated r row p e q old hp he (eq.symm.trans hq)

theorem FactorTrace.take {a : Pattern} {target start k : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) (bound : start ≤ k) : FactorTrace (a.take k) target start rows := by
  induction h with
  | single hp hn => exact .single (by simpa only [predecessor, rowAt_take bound] using hp) hn
  | cons hp hn inner ih =>
    exact .cons (by simpa only [predecessor, rowAt_take bound] using hp) hn (ih (by omega))

theorem Trace.take {a : Pattern} {target start k : Nat} {rows : List Nat}
    (h : Trace a target start rows) (bound : start ≤ k) : Trace (a.take k) target start rows := by
  induction h with
  | done => exact .done
  | step ht hp hn inner ih =>
    exact .step ht (by simpa only [predecessor, rowAt_take bound] using hp) hn (ih (by omega))

theorem take_markTrace {a : Pattern} {k r mark source : Nat} {row : Row} {trace : List Nat}
    (bound : r ≤ k) (hr : rowAt a r = some row) (below : mark < r)
    (paired : row.columns[row.columns.idxOf mark - row.step]? = some source)
    (computed : markTrace a r mark = some trace) : markTrace (a.take k) r mark = some trace := by
  obtain ⟨member, index, history⟩ := markTrace_spec hr paired computed
  have history' := history.take (by omega : mark ≤ k)
  have newRow := (rowAt_take bound).trans hr
  simp [markTrace, newRow, member, index, paired, traceFrom_iff.mpr history']

end IBLP
