import IBLP.ScanReach
import IBLP.RowUpdate
import IBLP.NativeRows

/-! Prefix proofs follow FullMarkedBLP ScanPrefix (Apache-2.0), with the
original canonical filtered frozen queue and arbitrary starting cursor. -/
namespace IBLP

theorem completeMark_other_row {a : Pattern} {rec : Records} {r mark i : Nat}
    (other : i ≠ r) : rowAt (completeMark a rec r mark) i = rowAt a i := by
  unfold completeMark
  split
  next row sources hr _ => exact rowAt_set_other hr other
  next => rfl

theorem completeMarks_fold_other_row (marks : List Nat) {a : Pattern} {rec : Records} {r i : Nat}
    (other : i ≠ r) :
    rowAt (marks.foldl (fun current mark => completeMark current rec r mark) a) i = rowAt a i := by
  induction marks generalizing a with
  | nil => rfl
  | cons mark marks ih =>
    simp only [List.foldl_cons]
    rw [ih, completeMark_other_row other]

theorem completeFrozenMarks_other_row {a : Pattern} {rec : Records} {r i : Nat}
    (other : i ≠ r) : rowAt (completeFrozenMarks a rec r) i = rowAt a i := by
  unfold completeFrozenMarks
  split
  · rfl
  · exact completeMarks_fold_other_row _ other

theorem scan_step_prefix_rowAt {a b : Pattern} {rec : Records} {r i : Nat} {sources : List Nat}
    (run : native (completeFrozenMarks a rec r) r = some (b, sources)) (before : i < r) :
    rowAt b i = rowAt a i := by
  rw [native_prefix_rowAt run before, completeFrozenMarks_other_row (by omega : i ≠ r)]

theorem ScanReach.initial_prefix {initial current : Pattern} {start cursor i : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) (before : i < start) : rowAt current i = rowAt initial i := by
  induction reach with
  | start => rfl
  | next previous _ run ih =>
    rw [scan_step_prefix_rowAt run (by have := previous.cursor_ge_start; omega)]
    exact ih

end IBLP
