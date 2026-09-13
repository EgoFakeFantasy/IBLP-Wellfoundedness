import IBLP.Realization.RawCopyData

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem rawCopyRowGraphData_old (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p : Nat} (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (r : FiniteRowIndex b) (row : IBLP.Row) (hr : rowAt b r.val = some row) (old : r.val < a.length) :
    (D.rawCopyRowGraphData nonempty copy hlast hm hp r row hr).graph.val =
      (D.graph ⟨r.val, r.property.1, old.le⟩).val := by
  simp only [rawCopyRowGraphData, dif_pos old]
  rfl

theorem rawCopyRowGraphData_new (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p : Nat} (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (r : FiniteRowIndex b) (row : IBLP.Row) (hr : rowAt b r.val = some row)
    (source : FiniteRowIndex a) (afterPrefix : a.length ≤ r.val)
    (owner : r.val = source.val + (a.length - p)) :
    (D.rawCopyRowGraphData nonempty copy hlast hm hp r row hr).graph =
      (D.lastExtension nonempty).embedding (D.graph source) := by
  have old : ¬r.val < a.length := by omega
  simp only [rawCopyRowGraphData, dif_neg old]
  congr 2
  apply Subtype.ext
  have actual := (IBLP.rawCopy_row_origin copy hlast hp afterPrefix hr).choose_spec.2.2.1
  change (IBLP.rawCopy_row_origin copy hlast hp afterPrefix hr).choose = source.val
  omega

theorem rawCopyData_graph_old (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p : Nat} (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (r : FiniteRowIndex b) (old : r.val < a.length) :
    ((D.rawCopyData nonempty proper copy hlast hm hp).graph r).val =
      (D.graph ⟨r.val, r.property.1, old.le⟩).val := by
  apply D.rawCopyRowGraphData_old nonempty copy hlast hm hp r _ _ old

theorem rawCopyData_graph_new (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p : Nat} (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (r : FiniteRowIndex b) (source : FiniteRowIndex a) (afterPrefix : a.length ≤ r.val)
    (owner : r.val = source.val + (a.length - p)) :
    (D.rawCopyData nonempty proper copy hlast hm hp).graph r =
      (D.lastExtension nonempty).embedding (D.graph source) := by
  apply D.rawCopyRowGraphData_new nonempty copy hlast hm hp r _ _ source afterPrefix owner

end IBLP.FiniteBoundedData
