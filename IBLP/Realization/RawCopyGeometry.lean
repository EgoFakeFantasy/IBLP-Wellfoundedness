import IBLP.RawCopy
import IBLP.Realization.CopyRowGeometry

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

include D in
theorem rawCopy_row_geometry {b : IBLP.Pattern} (proper : ProperMarks a)
    (copy : IBLP.rawCopy a = some b) {r : Nat} {row : IBLP.Row} (hr : rowAt b r = some row) :
    row.BasicValid r ∧ row.OrdinaryShape ∧ ∀ x ∈ row.marks, row.ProperMark x := by
  obtain ⟨last, p, _, hlast, hp, positive, included, _, _⟩ := IBLP.rawCopy_decomposition copy
  have nonempty : 0 < a.length := lt_of_lt_of_le positive included
  have atLast := IBLP.getLast_rowAt hlast
  have validLast := D.valid _ _ atLast
  have hasHead : 0 < last.columns.length := by have := validLast.2.1; omega
  let minimum := last.columns[0]'hasHead
  have hm : last.columns.head? = some minimum := by
    simp only [List.head?_eq_getElem?, List.getElem?_eq_getElem hasHead, minimum]
  by_cases old : r < a.length
  · have source : rowAt a r = some row := (IBLP.rawCopy_prefix copy old).symm.trans hr
    exact ⟨D.valid _ _ source, D.shapes row (rowAt_mem source), proper row (rowAt_mem source)⟩
  · obtain ⟨source, tail, _, owner, rowCopy⟩ := IBLP.rawCopy_row_origin copy hlast hp (by omega) hr
    obtain ⟨oldRow, atSource, _⟩ := Option.bind_eq_some_iff.mp rowCopy
    rw [owner]
    exact ⟨D.copyRow_valid nonempty atLast hm hp atSource tail rowCopy,
      D.copyRow_shape nonempty atLast hm hp atSource rowCopy,
      D.copyRow_proper nonempty atLast hm hp atSource
        (proper oldRow (rowAt_mem atSource)) rowCopy⟩

include D in
theorem rawCopy_geometry {b : IBLP.Pattern} (proper : ProperMarks a)
    (copy : IBLP.rawCopy a = some b) : BasicValid b ∧ OrdinaryShape b ∧ ProperMarks b := by
  have geometry {r : Nat} {row : IBLP.Row} (hr : rowAt b r = some row) :=
    D.rawCopy_row_geometry proper copy hr
  have rowExists (row : IBLP.Row) (member : row ∈ b) : ∃ r, rowAt b r = some row := by
    obtain ⟨i, hi, value⟩ := List.mem_iff_getElem.mp member
    refine ⟨i + 1, ?_⟩
    simp only [rowAt, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, List.getElem?_eq_getElem hi, value]
  refine ⟨fun _ _ hr => (geometry hr).1, ?_, ?_⟩
  · intro row member
    obtain ⟨r, hr⟩ := rowExists row member
    exact (geometry hr).2.1
  · intro row member
    obtain ⟨r, hr⟩ := rowExists row member
    exact (geometry hr).2.2

end IBLP.FiniteBoundedData
