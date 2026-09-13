import IBLP.ScanLabels
import IBLP.ScanPrefix

namespace IBLP

/-- Every unprocessed entrance row has its literal old columns, step,
and marks, uniformly renamed by the actual insertion map. This statement
depends only on the original program, not on event geometry. -/
theorem ScanLabeledReach.unprocessed_rowAt {initial current : Pattern}
    {start oldCursor i : Nat} {rec : Records} {names : Nat → Nat} {row : Row}
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (unprocessed : oldCursor ≤ i) (atRow : rowAt initial i = some row) :
    rowAt current (names i) = some ⟨row.columns.map names, row.step, row.marks.map names⟩ := by
  induction reach with
  | start => simpa only [id_eq, List.map_id] using atRow
  | @next before after records old name sources previous bound run ih =>
    have behind := previous.names_strictMono (by omega : old < i)
    have atOld := ih (by omega)
    have atMarked : rowAt (completeFrozenMarks before records (name old)) (name i) =
        some ⟨row.columns.map name, row.step, row.marks.map name⟩ :=
      (completeFrozenMarks_other_row (by omega : name i ≠ name old)).trans atOld
    simp only [Function.comp_apply, shiftAfter, if_pos behind]
    rw [native_suffix_rowAt run behind, atMarked]
    simp only [Option.map_some, Row.shiftAfter, List.map_map, Function.comp_def]

end IBLP
