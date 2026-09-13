import IBLP.Realization.NativeData

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
  (sourcesRun : IBLP.nativeSources a r.val = some sources) (proper : IBLP.ProperMarks a)
  {b : IBLP.Pattern} (run : IBLP.native a r.val = some (b, sources))

theorem nativeData_graph_prefix (i : FiniteRowIndex b) (before : i.val < r.val) :
    (D.nativeData r hr hp he sourcesRun proper run).graph i =
      D.graph ⟨i.val, i.property.1, by have := r.property.2; omega⟩ := by
  change (D.nativeRowGraphData r hr hp he sourcesRun proper run i _ _).graph = _
  simp only [nativeRowGraphData, dif_pos before]
  rfl

theorem nativeData_graph_family (i : FiniteRowIndex b) (lower : r.val ≤ i.val)
    (upper : i.val ≤ r.val + sources.length) :
    (D.nativeData r hr hp he sourcesRun proper run).graph i =
      D.nativeFamilyGraph r hr hp he sourcesRun (i.val - r.val) := by
  change (D.nativeRowGraphData r hr hp he sourcesRun proper run i _ _).graph = _
  simp only [nativeRowGraphData, dif_neg (by omega : ¬ i.val < r.val), dif_pos upper]
  rfl

theorem nativeData_graph_suffix (i : FiniteRowIndex b) (after : r.val + sources.length < i.val) :
    (D.nativeData r hr hp he sourcesRun proper run).graph i =
      D.graph ⟨i.val - sources.length, by have := r.property.1; omega,
        by have := i.property.2; have := IBLP.native_length run; omega⟩ := by
  change (D.nativeRowGraphData r hr hp he sourcesRun proper run i _ _).graph = _
  simp only [nativeRowGraphData, dif_neg (by omega : ¬ i.val < r.val),
    dif_neg (by omega : ¬ i.val ≤ r.val + sources.length)]
  rfl

end IBLP.FiniteBoundedData
