import IBLP.Realization.CopyRecordInheritance
import IBLP.SeedRecordStep

namespace IBLP.BoundedRealization
universe u

/-- Manuscript 6.2: every actual nonempty record in a copied block inherits
an actual record at its entrance p-chain seed. Strong induction on the old
cursor discharges all earlier seed-history premises used in q inheritance.
Only strictly earlier actual completion geometry remains as a premise. -/
theorem copies_scan_seed_history {stage : ModelStage.{u}} {a copied initial current : Pattern}
    (R : BoundedRealization stage a) {last : Row} {p m k oldCursor : Nat}
    {rec : Records} {names : Nat → Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) (within : k < m)
    (reach : ScanLabeledReach initial a.length current rec oldCursor names)
    (earlierRows : ScanPriorGeometry initial a.length (names oldCursor)) :
    SeedRecordHistory initial (a.length + k * (a.length - p))
      (a.length + (k + 1) * (a.length - p)) rec names := by
  obtain ⟨next, _, copiedRealization, _, _⟩ := R.toMarkedRealization.rawCopies_realization_exists m copies
  obtain ⟨entry, _, _⟩ := copiedRealization.cut_realization_exists cut
  have parentPositive : 0 < a.length := rowAt_pos (getLast_rowAt hlast)
  induction oldCursor using Nat.strong_induction_on generalizing current rec names with
  | h cursor ih =>
    cases reach with
    | start => exact SeedRecordHistory.empty _ _ _ _
    | @next before after records old name sources previous bound run =>
      have earlier : name old < (shiftAfter (name old) sources.length ∘ name) (old + 1) := by
        rw [previous.next_cursor]
        omega
      have previousGeometry := earlierRows.mono earlier.le
      have previousSeeds := ih old (by omega) previous previousGeometry
      apply previousSeeds.native_step previous
      intro nonempty lower upper
      have oldLength := previous.length_balance
      have included : old ≤ initial.length := by omega
      obtain ⟨row, atOriginal⟩ := rowAt_exists (by omega : 0 < old) included
      have shape := entry.data.shapes row (rowAt_mem atOriginal)
      obtain ⟨v, originalP⟩ := fromRight_exists (xs := row.columns) (k := row.step + 1)
        (by omega) (by have := Row.step_lt_length shape; omega)
      obtain ⟨e, originalE⟩ := fromRight_exists (xs := row.columns) (Row.step_pos shape) (Row.step_lt_length shape).le
      change row.p = some v at originalP
      change row.e = some e at originalE
      have pred : predecessor initial old = some v := by simp [predecessor, atOriginal, originalP]
      have vBefore := predecessor_lt entry.data.valid entry.data.shapes pred
      by_cases stays : a.length + k * (a.length - p) ≤ v
      · have ownerGeometry := earlierRows before records (name old) previous.forget earlier
        have earlierSeeds : ∀ j, a.length + k * (a.length - p) ≤ j →
            j < a.length + (k + 1) * (a.length - p) → j < old →
            ∀ birth history birthNames,
            ScanLabeledReach initial a.length birth history j birthNames → birthNames j < name old →
            SeedRecordHistory initial (a.length + k * (a.length - p))
              (a.length + (k + 1) * (a.length - p)) history birthNames := by
          intro j _ _ prior birth history birthNames atBirth beforeOwner
          exact ih j (by omega) atBirth (previousGeometry.mono beforeOwner.le)
        obtain ⟨saved, record, exactSources, sameSeed⟩ := R.copies_scan_record_inherits
          hlast hp copies cut within upper stays atOriginal originalP originalE previous previousGeometry
          ownerGeometry earlierSeeds run nonempty
        obtain ⟨seedSources, seedRecord, width⟩ := previousSeeds v saved stays (vBefore.trans upper) record
        refine ⟨seedSources, ?_, ?_⟩
        · rw [sameSeed]
          exact List.mem_cons_of_mem _ seedRecord
        · rw [exactSources, descendingPacket_length]
          exact width
      · have seed := blockSeed_stop pred (by omega : v < a.length + k * (a.length - p))
        refine ⟨sources, ?_, rfl⟩
        rw [seed]
        exact List.mem_cons_self ..

end IBLP.BoundedRealization
