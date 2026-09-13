import IBLP.ScanSaturation
import IBLP.NativeRows

namespace IBLP

/-- The original finite fuel succeeds whenever each actual native input
has the already proved ordinary syntax. Every transition consumes one
old row, regardless of the number of newly inserted family rows. -/
theorem scanFuel_total_of_history {initial : Pattern} {start : Nat}
    (positive : 0 < start) (history : ScanSyntaxHistory initial start) :
    ∀ fuel current rec cursor, ScanReach initial start current rec cursor →
      current.length + 1 ≤ cursor + fuel → ∃ result, scanFuel fuel current rec cursor = some result := by
  intro fuel
  induction fuel with
  | zero =>
    intro current rec cursor reach room
    exact ⟨current, by simp only [scanFuel, if_pos (show current.length < cursor by omega)]⟩
  | succ fuel ih =>
    intro current rec cursor reach room
    by_cases ended : current.length < cursor
    · exact ⟨current, by simp only [scanFuel, if_pos ended]⟩
    · have entrance := history current rec cursor reach
      have positiveCursor := positive.trans_le reach.cursor_ge_start
      obtain ⟨row, atRow⟩ := rowAt_exists (a := completeFrozenMarks current rec cursor)
        positiveCursor (by rw [completeFrozenMarks_length]; omega)
      obtain ⟨after, sources, run⟩ := native_total entrance.1 entrance.2.1 atRow
      have length := native_length run
      rw [completeFrozenMarks_length] at length
      obtain ⟨result, finished⟩ := ih after
        (if sources.isEmpty then rec else (cursor, sources) :: rec) (cursor + sources.length + 1)
        (.next reach (by omega) run) (by omega)
      exact ⟨result, by simp only [scanFuel, if_neg ended, run, Bind.bind, Option.bind, finished]⟩

theorem scan_total_of_history {initial : Pattern} {start : Nat}
    (positive : 0 < start) (history : ScanSyntaxHistory initial start) :
    ∃ result, scan initial start = some result :=
  scanFuel_total_of_history positive history (initial.length + 1 - start) initial [] start .start (by omega)

end IBLP
