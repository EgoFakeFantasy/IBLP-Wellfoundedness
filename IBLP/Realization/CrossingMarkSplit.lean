import IBLP.CrossingTraceSpec
import IBLP.Realization.MarkedRealization
import IBLP.MarkTraceSpec

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

include R in
theorem crossing_mark_split {row : IBLP.Row} {r mark p bottom boundary : Nat} {trace : List Nat}
    (hr : rowAt a r = some row) (marked : mark ∈ row.marks)
    (computed : IBLP.markTrace a r mark = some trace) (bottomAt : IBLP.fromRight trace 2 = some bottom)
    (crossing : bottom < p) (found : trace.find? (· < p) = some boundary) :
    ∃ source front suffix, row.columns[row.columns.idxOf mark - row.step]? = some source ∧
      trace.dropLast = front ++ suffix ∧ FactorPrefix a boundary mark front ∧
      FactorTrace a source boundary suffix ∧ (∀ r ∈ front, p ≤ r) ∧ boundary < p := by
  obtain ⟨source, history, paired, historyAt, factors, _⟩ := R.marks r row mark hr marked
  have same : history = trace := Option.some.inj (historyAt.symm.trans computed)
  subst history
  have historyShape := (IBLP.markTrace_spec hr paired computed).2.2.unique factors.toTrace
  have bottom : IBLP.fromRight (trace.dropLast ++ [source]) 2 = some bottom := by rw [← historyShape]; exact bottomAt
  have first : (trace.dropLast ++ [source]).find? (· < p) = some boundary := by rw [← historyShape]; exact found
  obtain ⟨front, suffix, split, before, after, tail, below⟩ :=
    factors.split_first_below (factors.first_below_factors bottom crossing first)
  exact ⟨source, front, suffix, paired, split, before, after, tail, below⟩

end IBLP.MarkedRealization
