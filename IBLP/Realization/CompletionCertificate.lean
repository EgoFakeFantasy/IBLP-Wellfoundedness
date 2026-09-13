import IBLP.Realization.CompletionData
import IBLP.CompletionTrace
import IBLP.Realization.TraceGraphCongruence
import IBLP.Realization.MarkGraphCongruence

namespace IBLP.FiniteBoundedData
universe u
variable {stage : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData stage a)
variable (r : FiniteRowIndex a) {row : Row} {mark : Nat} {sources : List Nat}
variable (hr : rowAt a r.val = some row) (C : row.CompletionGeometry r.val mark sources)
variable (proper : ∀ z ∈ row.marks, row.ProperMark z)
variable (packet : ∀ s ∈ sources, D.nativeImage r s = D.point (mark + 1 + (sources.filter (· < s)).length))

theorem completion_traceGraph {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) :
    D.traceGraph h = (D.completionData r hr C proper packet).traceGraph
      (h.completion hr (D.valid _ _ hr) (D.shapes row (rowAt_mem hr)) C) := by
  apply D.traceGraph_congr_rows (D.completionData r hr C proper packet) h
    (h.completion hr (D.valid _ _ hr) (D.shapes row (rowAt_mem hr)) C)
  have build (xs : List Nat) : List.Forall₂
      (D.RowGraphsEqual (D.completionData r hr C proper packet)) xs xs := by
    induction xs with
    | nil => constructor
    | cons i xs ih =>
      refine .cons ?_ ih
      intro oldValid newValid
      rfl
  exact build rows

/-- All old complete weak certificates transport through completion,
including certificates whose carrier is above the edited row. -/
theorem completion_markCertificate (i : FiniteRowIndex a)
    (j : FiniteRowIndex (a.set (r.val - 1) (completeMarkRow row mark sources))) (owner : i.val = j.val)
    {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) :
    h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows i.val ↔
      (h.completion hr (D.valid _ _ hr) (D.shapes row (rowAt_mem hr)) C).MarkCertificate
        (D.completionData r hr C proper packet).toFiniteTraceRows.toInternalTraceRows j.val := by
  apply D.markCertificate_congr_graphs (D.completionData r hr C proper packet) i j h
    (h.completion hr (D.valid _ _ hr) (D.shapes row (rowAt_mem hr)) C)
  · rw [D.completionData_graph]
    congr 1
    exact Subtype.ext owner
  · exact D.completion_traceGraph r hr C proper packet h

end IBLP.FiniteBoundedData
