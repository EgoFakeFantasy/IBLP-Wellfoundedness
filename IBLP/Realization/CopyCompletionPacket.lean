import IBLP.Realization.CopyParallelCertificate
import IBLP.Realization.CopyTargetGap
import IBLP.Realization.PacketGeometry

namespace IBLP.BoundedRealization
universe u

set_option maxHeartbeats 600000 in
/-- Both packets and all full weak certificates for the actual next
frozen event. Their derivation consumes only earlier geometry and the
historical restriction invariant, never the current completion itself. -/
theorem copies_scan_completion_packet {stage savedStage : ModelStage.{u}}
    {a copied initial before current : Pattern}
    (R : BoundedRealization stage a) (entry : MarkedRealization savedStage initial)
    (E : FiniteBoundedData savedStage current)
    {last row currentRow : Row} {p m k oldCursor mark : Nat}
    {rec : Records} {names : Nat → Nat} {pending sources : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ oldCursor)
    (upper : oldCursor < a.length + (k + 1) * (a.length - p))
    (atOriginal : rowAt initial oldCursor = some row) (marked : mark ∈ row.marks)
    (reach : ScanLabeledReach initial a.length before rec oldCursor names)
    (frozen : FrozenReach before rec (names oldCursor) current (names mark :: pending))
    (earlierRows : ScanPriorGeometry initial a.length (names oldCursor))
    (earlierMarks : FrozenGeometryBefore before rec (names oldCursor) (names mark :: pending).length)
    (atCurrent : rowAt current (names oldCursor) = some currentRow)
    (history : entry.data.FamilyRestrictionHistory E names)
    (completed : completionRecord current rec (names oldCursor) (names mark) = some sources) :
    ∃ C : currentRow.CompletionGeometry (names oldCursor) (names mark) sources,
      E.CompletionHistoryPacket (names oldCursor) (names mark) sources := by
  have H := R.copies_scan_parallel_certificate entry E hlast hp copies cut within lower upper
    atOriginal marked reach frozen earlierRows earlierMarks atCurrent history completed
  have targetGap := R.copies_scan_target_gap hlast hp copies cut within lower upper
    atOriginal marked reach frozen earlierRows earlierMarks atCurrent completed
  have entrance := reach.forget.syntax_of_geometry entry.data.valid entry.data.shapes entry.proper earlierRows
  have atBefore := reach.unprocessed_rowAt le_rfl atOriginal
  have originalProper := entrance.2.2 _ (rowAt_mem atBefore) (names mark)
    (List.mem_map.mpr ⟨mark, marked, rfl⟩)
  have proper := frozen.proper_mark entrance.1 entrance.2.1 entrance.2.2 earlierMarks
    atBefore atCurrent originalProper
  obtain ⟨_, bottom, _, _, lookup, _, _⟩ := completionRecord_iff.mp completed
  have record := recordAt_mem lookup
  have bounds := reach.forget.record_source_bounds
    (earlierRows.priorSyntax entry.data.valid entry.data.shapes entry.proper) record
  have beforeOwner := reach.forget.record_family_before record
  let owner : FiniteRowIndex current := ⟨names oldCursor, rowAt_pos atCurrent, rowAt_le_length atCurrent⟩
  obtain ⟨C⟩ := E.completionGeometry_of_packet owner atCurrent proper
    (bounds.1.imp Nat.ne_of_gt) (by
      intro s member
      have := (bounds.2 s member).2
      have := rowAt_le_length atCurrent
      omega)
    targetGap.1 targetGap.2 (H.edge E)
  exact ⟨C, H⟩

end IBLP.BoundedRealization
