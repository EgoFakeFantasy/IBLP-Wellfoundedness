import IBLP.ScanStepQ
import IBLP.ScanRowBirth
import IBLP.ScanOldMarkTrace

namespace IBLP

/-- For every processed old row, its current q either is the original q
under the current old-label map, or comes from an actual earlier frozen
completion at precisely that original label. Native adds no hidden change. -/
theorem ScanLabeledReach.processed_q_origin {initial current : Pattern}
    {start oldCursor i oldQ : Nat} {rec : Records} {names : Nat → Nat} {row : Row}
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : ScanPriorGeometry initial start (names oldCursor))
    (scanned : start ≤ i) (processed : i < oldCursor)
    (atOriginal : rowAt initial i = some row) (originalQ : row.q = some oldQ) :
    ∃ q, penultimate current (names i) = some q ∧
      (q = names oldQ ∨ oldQ ∈ row.marks ∧ ∃ before records,
        ScanReach initial start before records (names i) ∧
        FrozenRaisedQ before records (names i) (names oldQ) 0 q) := by
  obtain ⟨before, records, after, sources, birthNames, event, run, labels, _, unchanged⟩ :=
    reach.processed_step scanned processed
  have atI := labels i (Nat.le_refl _)
  have earlier : birthNames i < names oldCursor := by rw [atI]; exact reach.names_strictMono processed
  have atBirth := event.unprocessed_rowAt (Nat.le_refl _) atOriginal
  have qBirth : (Row.mk (row.columns.map birthNames) row.step (row.marks.map birthNames)).q =
      some (birthNames oldQ) := by
    change fromRight (row.columns.map birthNames) 2 = _
    rw [fromRight_map]
    change row.q.map birthNames = _
    rw [originalQ]
    rfl
  have birthSyntax := event.forget.syntax_of_geometry valid shapes proper (history.mono earlier.le)
  have birthGeometry := history before records (birthNames i) event.forget earlier
  obtain ⟨q, afterQ, origin⟩ := scan_step_q_origin birthSyntax.1 birthSyntax.2.1 birthSyntax.2.2
    atBirth qBirth birthGeometry run
  have below : oldQ < i := penultimate_lt valid (by simp [penultimate, atOriginal, originalQ])
  have atQ := labels oldQ below.le
  have currentQ : penultimate current (names i) = some q := by
    rw [atI] at afterQ
    simpa only [penultimate, unchanged (names i) (Nat.le_add_right _ _)] using afterQ
  refine ⟨q, currentQ, ?_⟩
  rcases origin with same | raised
  · exact Or.inl (same.trans atQ)
  · right
    have member := raised.original_mark atBirth
    change birthNames oldQ ∈ row.marks.map birthNames at member
    obtain ⟨oldMark, marked, same⟩ := List.mem_map.mp member
    have equal := event.names_strictMono.injective same
    subst oldMark
    refine ⟨marked, before, records, ?_, ?_⟩
    · simpa only [atI] using event.forget
    · simpa only [atI, atQ] using raised

end IBLP
