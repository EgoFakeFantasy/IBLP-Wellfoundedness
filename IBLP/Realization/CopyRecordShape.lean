import IBLP.Realization.CopySeedHistory
import IBLP.ScanLabeledRecordBirth

namespace IBLP.BoundedRealization
universe u

/-- The exact current source list of every retained in-block old record.
All prior seed hypotheses are now discharged by the proved strong
induction, leaving only strictly earlier completion geometry. -/
theorem copies_scan_record_shape {stage : ModelStage.{u}} {a copied initial current : Pattern}
    (R : BoundedRealization stage a) {last row : Row} {p m k i v oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} {sources : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) (within : k < m)
    (upper : i < a.length + (k + 1) * (a.length - p))
    (vInBlock : a.length + k * (a.length - p) ≤ v)
    (atOriginal : rowAt initial i = some row) (originalP : row.p = some v)
    (reach : ScanLabeledReach initial a.length current rec oldCursor names)
    (earlierRows : ScanPriorGeometry initial a.length (names oldCursor))
    (record : (names i, sources) ∈ rec) : sources = descendingPacket (names v) sources.length := by
  obtain ⟨next, _, copiedRealization, _, _⟩ := R.toMarkedRealization.rawCopies_realization_exists m copies
  obtain ⟨entry, _, _⟩ := copiedRealization.cut_realization_exists cut
  have shape := entry.data.shapes row (rowAt_mem atOriginal)
  obtain ⟨e, originalE⟩ := fromRight_exists (xs := row.columns) (Row.step_pos shape) (Row.step_lt_length shape).le
  obtain ⟨before, records, after, birthNames, birth, run, labels⟩ := reach.record_birth record
  have atI := labels i (Nat.le_refl _)
  have behind := reach.forget.record_family_before record
  have earlier : birthNames i < names oldCursor := by rw [atI]; omega
  have beforeGeometry := earlierRows.mono earlier.le
  have ownerGeometry := earlierRows before records (birthNames i) birth.forget earlier
  have earlierSeeds : ∀ j, a.length + k * (a.length - p) ≤ j →
      j < a.length + (k + 1) * (a.length - p) → j < i →
      ∀ event history eventNames,
      ScanLabeledReach initial a.length event history j eventNames → eventNames j < birthNames i →
      SeedRecordHistory initial (a.length + k * (a.length - p))
        (a.length + (k + 1) * (a.length - p)) history eventNames := by
    intro j _ _ _ event history eventNames eventReach eventBefore
    exact R.copies_scan_seed_history hlast hp copies cut within eventReach (beforeGeometry.mono eventBefore.le)
  obtain ⟨saved, _, exactSources, _⟩ := R.copies_scan_record_inherits hlast hp copies cut within
    upper vInBlock atOriginal originalP originalE birth beforeGeometry ownerGeometry earlierSeeds run
    (reach.forget.records_nonempty _ record)
  have pred : predecessor initial i = some v := by simp [predecessor, atOriginal, originalP]
  have vBefore := predecessor_lt entry.data.valid entry.data.shapes pred
  have atV := labels v vBefore.le
  have width : sources.length = saved.length := by rw [exactSources, descendingPacket_length]
  simpa only [atV, ← width] using exactSources

end IBLP.BoundedRealization
