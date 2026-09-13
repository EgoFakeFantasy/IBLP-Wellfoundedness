import IBLP.Realization.CopyScanFamily

namespace IBLP.MarkedRealization
universe u

/-- A processed copied row has q at its entrance q label or at the last
point of that label's own native family. The seed-width premise concerns
only the strictly earlier entrance at this processed row, not the current
cursor. Its eventual induction proof is not assumed here to be complete. -/
theorem copies_scan_q_last {stage : ModelStage.{u}} {a copied initial current : Pattern}
    (R : MarkedRealization stage a) {last row : Row} {p m k i oldQ oldCursor : Nat}
    {rec : Records} {names : Nat → Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ i)
    (upper : i < a.length + (k + 1) * (a.length - p))
    (atOriginal : rowAt initial i = some row) (originalQ : row.q = some oldQ)
    (reach : ScanLabeledReach initial a.length current rec oldCursor names) (processed : i < oldCursor)
    (earlierRows : ScanPriorGeometry initial a.length (names oldCursor))
    (earlierSeeds : ∀ before records birthNames,
      ScanLabeledReach initial a.length before records i birthNames → birthNames i < names oldCursor →
      SeedRecordHistory initial (a.length + k * (a.length - p))
        (a.length + (k + 1) * (a.length - p)) records birthNames) :
    ∃ q, penultimate current (names i) = some q ∧
      (q = names oldQ ∨ q + 1 = names (oldQ + 1)) := by
  obtain ⟨next, _, copiedRealization, _, _⟩ := R.rawCopies_realization_exists m copies
  obtain ⟨entry, _, _⟩ := copiedRealization.cut_realization_exists cut
  obtain ⟨before, records, after, ss, birthNames, event, run, labels, _, unchanged⟩ :=
    reach.processed_step (by omega) processed
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
  have birthSyntax := event.forget.syntax_of_geometry entry.data.valid entry.data.shapes entry.proper
    (earlierRows.mono earlier.le)
  have birthGeometry := earlierRows before records (birthNames i) event.forget earlier
  obtain ⟨q, afterQ, origin⟩ := scan_step_q_origin birthSyntax.1 birthSyntax.2.1 birthSyntax.2.2
    atBirth qBirth birthGeometry run
  have below : oldQ < i := penultimate_lt entry.data.valid (by simp [penultimate, atOriginal, originalQ])
  have currentQ : penultimate current (names i) = some q := by
    rw [atI] at afterQ
    simpa only [penultimate, unchanged (names i) (Nat.le_add_right _ _)] using afterQ
  refine ⟨q, currentQ, ?_⟩
  rcases origin with same | raised
  · exact Or.inl (same.trans (labels oldQ below.le))
  · have member := raised.original_mark atBirth
    change birthNames oldQ ∈ row.marks.map birthNames at member
    obtain ⟨oldMark, marked, same⟩ := List.mem_map.mp member
    have equal := event.names_strictMono.injective same
    subst oldMark
    obtain ⟨atEvent, pending, eventRow, eventSources, frozen, _, _, _, guard, _, value⟩ := raised
    obtain ⟨saved, _, width, family, _⟩ := R.copies_scan_completion_family hlast hp copies cut within
      lower upper atOriginal marked event frozen (earlierRows.mono earlier.le)
      (birthGeometry.mono (Nat.zero_le _)) (earlierSeeds before records birthNames event earlier) guard
    have atNext := labels (oldQ + 1) (by omega)
    right
    rw [← atNext]
    omega

/-- In particular q cannot cross the next entrance label. This is the
inequality used to exclude a strictly smaller old q in record inheritance. -/
theorem copies_scan_q_interval {stage : ModelStage.{u}} {a copied initial current : Pattern}
    (R : MarkedRealization stage a) {last row : Row} {p m k i oldQ oldCursor q : Nat}
    {rec : Records} {names : Nat → Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ i)
    (upper : i < a.length + (k + 1) * (a.length - p))
    (atOriginal : rowAt initial i = some row) (originalQ : row.q = some oldQ)
    (reach : ScanLabeledReach initial a.length current rec oldCursor names) (processed : i < oldCursor)
    (earlierRows : ScanPriorGeometry initial a.length (names oldCursor))
    (earlierSeeds : ∀ before records birthNames,
      ScanLabeledReach initial a.length before records i birthNames → birthNames i < names oldCursor →
      SeedRecordHistory initial (a.length + k * (a.length - p))
        (a.length + (k + 1) * (a.length - p)) records birthNames)
    (currentQ : penultimate current (names i) = some q) : q < names (oldQ + 1) := by
  obtain ⟨actual, atActual, cases⟩ := R.copies_scan_q_last hlast hp copies cut within lower upper
    atOriginal originalQ reach processed earlierRows earlierSeeds
  have same := Option.some.inj (atActual.symm.trans currentQ)
  subst actual
  rcases cases with same | next
  · rw [same]
    exact reach.names_strictMono (Nat.lt_succ_self _)
  · omega

end IBLP.MarkedRealization
