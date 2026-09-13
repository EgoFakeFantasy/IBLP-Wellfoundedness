import IBLP.Realization.CopyCompletionPacket
import IBLP.Realization.FrozenEventInduction

namespace IBLP.BoundedRealization
universe u

/-- Close every actual mark of one copied-block row. The inner frozen
induction discharges all earlier-mark geometry premises and produces the
complete marked realization with its saved-graph invariant and same top.
Only strictly earlier scan rows remain for the outer induction. -/
theorem copies_frozen_closure {stage savedStage : ModelStage.{u}}
    {a copied initial before : Pattern}
    (R : BoundedRealization stage a) (entry : MarkedRealization savedStage initial)
    (S : MarkedRealization savedStage before)
    {last row : Row} {p m k oldCursor : Nat} {rec : Records} {names : Nat → Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ oldCursor)
    (upper : oldCursor < a.length + (k + 1) * (a.length - p))
    (atOriginal : rowAt initial oldCursor = some row)
    (reach : ScanLabeledReach initial a.length before rec oldCursor names)
    (earlierRows : ScanPriorGeometry initial a.length (names oldCursor))
    (history : entry.data.FamilyRestrictionHistory S.data names) :
    FrozenGeometryBefore before rec (names oldCursor) 0 ∧
      ∃ T : MarkedRealization savedStage (completeFrozenMarks before rec (names oldCursor)),
        T.top = S.top ∧ entry.data.FamilyRestrictionHistory T.data names := by
  apply S.frozen_realization_from_event_step entry.data rec (names oldCursor) names history
  intro current mark pending frozen earlierMarks T currentHistory currentRow sources atCurrent completed
  have atBefore := reach.unprocessed_rowAt le_rfl atOriginal
  have queued := frozen.pending_mem (List.mem_cons_self ..)
  simp only [frozenMarks, atBefore, mem_canonicalColumns, List.mem_filter] at queued
  obtain ⟨oldMark, marked, image⟩ := List.mem_map.mp queued.1
  subst mark
  exact R.copies_scan_completion_packet entry T.data hlast hp copies cut within lower upper
    atOriginal marked reach frozen earlierRows earlierMarks atCurrent currentHistory completed

end IBLP.BoundedRealization
