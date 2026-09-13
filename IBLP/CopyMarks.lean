import IBLP.Realization.CopyRowGeometry

namespace IBLP

theorem copyRow_kept_mark {a : Pattern} {last row copied : Row} {r mark imageMark : Nat}
    (hr : rowAt a r = some row) (rowCopy : copyRow a last r = some copied)
    (marked : mark ∈ row.marks) (column : mark ∈ row.columns)
    (kept : keepCopiedMark a last r row copied.columns mark = true)
    (image : copyEntry a.length last mark = some imageMark) : imageMark ∈ copied.marks := by
  obtain ⟨cols, marks, _, marksMap, rfl⟩ := FiniteBoundedData.copyRow_description hr rowCopy
  apply (mem_canonicalColumns imageMark marks).mpr
  have selected : mark ∈ row.marks.filter (fun y => y ∈ row.columns &&
      keepCopiedMark a last r row (canonicalColumns cols) y) := by
    apply List.mem_filter.mpr
    exact ⟨marked, by simp [column, kept]⟩
  obtain ⟨value, member, image'⟩ := mapped_mem_left (FullMarkedBLP.option_mapM_forall2 marksMap) selected
  have same := Option.some.inj (image'.symm.trans image)
  exact same ▸ member

theorem keepCopiedMark_full {a : Pattern} {last row : Row} {r mark minimum p bottom : Nat}
    {trace cols : List Nat} (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (computed : markTrace a r mark = some trace) (bottomAt : fromRight trace 2 = some bottom)
    (full : p ≤ bottom) : keepCopiedMark a last r row cols mark = true := by
  simp [keepCopiedMark, hm, hp, computed, bottomAt, full]

end IBLP
