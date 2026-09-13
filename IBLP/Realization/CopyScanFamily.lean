import IBLP.Realization.CopyScanRecords
import IBLP.SeedRecordHistory

namespace IBLP.MarkedRealization
universe u

/-- Once the prior seed-record induction invariant is supplied, the
actual source width read by a copied mark is exactly its own saved family
width. Its entire target packet therefore contains no entrance label.
Proving that seed invariant for all scan stages is still a separate task. -/
theorem copies_scan_completion_family {stage : ModelStage.{u}} {a copied initial before current : Pattern}
    (R : MarkedRealization stage a) {last row : Row} {p m k oldCursor mark : Nat}
    {rec : Records} {names : Nat → Nat} {pending sources : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ oldCursor)
    (upper : oldCursor < a.length + (k + 1) * (a.length - p))
    (atOriginal : rowAt initial oldCursor = some row) (marked : mark ∈ row.marks)
    (reach : ScanLabeledReach initial a.length before rec oldCursor names)
    (frozen : FrozenReach before rec (names oldCursor) current pending)
    (earlierRows : ScanPriorGeometry initial a.length (names oldCursor))
    (earlierMarks : FrozenGeometryBefore before rec (names oldCursor) pending.length)
    (seedHistory : SeedRecordHistory initial (a.length + k * (a.length - p))
      (a.length + (k + 1) * (a.length - p)) rec names)
    (completed : completionRecord current rec (names oldCursor) (names mark) = some sources) :
    ∃ saved, (names mark, saved) ∈ rec ∧ saved.length = sources.length ∧
      names (mark + 1) = names mark + sources.length + 1 ∧
      (∀ j, 0 < j → j ≤ sources.length → ∀ i, names i ≠ names mark + j) := by
  obtain ⟨target, trace, bottom, _, bottomAt, _, factors, bottomRecord, facts⟩ :=
    R.copies_scan_completion_factors hlast hp copies cut within lower upper atOriginal marked
      reach frozen earlierRows earlierMarks completed
  have atMark := facts mark factors.start_mem
  have bottomMember : bottom ∈ trace.dropLast :=
    List.mem_of_getLast? ((fromRight_two_dropLast trace).symm.trans bottomAt)
  have atBottom := facts bottom bottomMember
  obtain ⟨saved, markRecord⟩ := atMark.2.2.2
  have width := seedHistory.same_width reach atMark.1 (atMark.2.1.trans upper)
    atBottom.1 (atBottom.2.1.trans upper) atBottom.2.2.1.symm markRecord bottomRecord
  obtain ⟨old, _, _, atOld, next⟩ := reach.record_neighbors markRecord
  have same : old = mark := reach.names_strictMono.injective atOld
  subst old
  refine ⟨saved, markRecord, width, ?_, ?_⟩
  · simpa only [width] using next
  · intro j positive bound i
    exact reach.record_family_not_old markRecord positive (by omega) i

end IBLP.MarkedRealization
