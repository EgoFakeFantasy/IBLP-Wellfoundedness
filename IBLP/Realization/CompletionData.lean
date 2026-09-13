import IBLP.Realization.CompletionEdges
import IBLP.Realization.ReplaceData

namespace IBLP.FiniteBoundedData
universe u
variable {stage : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData stage a)
variable (r : FiniteRowIndex a) {row : Row} {mark : Nat} {sources : List Nat}
variable (hr : rowAt a r.val = some row) (C : row.CompletionGeometry r.val mark sources)
variable (proper : ∀ z ∈ row.marks, row.ProperMark z)
variable (packet : ∀ s ∈ sources, D.nativeImage r s = D.point (mark + 1 + (sources.filter (· < s)).length))

/-- Complete finite data after a geometrically and semantically justified
row completion. Deriving the two packet premises from scan history is
reserved for the event induction. -/
noncomputable def completionData :
    FiniteBoundedData stage (a.set (r.val - 1) (completeMarkRow row mark sources)) :=
  D.replaceData r hr _ (D.completionRowData r hr C packet) rfl
    (C.basic_valid (D.valid _ _ hr) (D.shapes row (rowAt_mem hr)) proper)
    (C.shape (D.valid _ _ hr).1 (D.shapes row (rowAt_mem hr)))

theorem completionData_point (i : Nat) : (D.completionData r hr C proper packet).point i = D.point i :=
  D.replaceData_point r hr _ _ _ _ _ i

theorem completionData_top : (D.completionData r hr C proper packet).top = D.top :=
  D.replaceData_top r hr _ _ _ _ _

theorem completionData_graph (i : FiniteRowIndex (a.set (r.val - 1) (completeMarkRow row mark sources))) :
    (D.completionData r hr C proper packet).graph i =
      D.graph (replaceRowIndex r.val (completeMarkRow row mark sources) i) := rfl

end IBLP.FiniteBoundedData
