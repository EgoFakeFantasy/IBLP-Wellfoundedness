import IBLP.Realization.CopyParallelPacket
import IBLP.Realization.ParallelWordRestriction
import IBLP.Realization.FamilyRestrictionHistory

namespace IBLP.BoundedRealization
universe u

/-- Full weak certificates for a literal successful copied-block packet.
The remaining semantic history premise says only that actual stored rows
are restrictions of their entrance graphs; it is preserved by the actual
native and completion constructors. No current-event geometry is assumed. -/
theorem copies_scan_parallel_certificate {stage savedStage : ModelStage.{u}}
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
    (frozen : FrozenReach before rec (names oldCursor) current pending)
    (earlierRows : ScanPriorGeometry initial a.length (names oldCursor))
    (earlierMarks : FrozenGeometryBefore before rec (names oldCursor) pending.length)
    (atCurrent : rowAt current (names oldCursor) = some currentRow)
    (history : entry.data.FamilyRestrictionHistory E names)
    (completed : completionRecord current rec (names oldCursor) (names mark) = some sources) :
    E.CompletionHistoryPacket (names oldCursor) (names mark) sources := by
  obtain ⟨target, trace, bottom, computed, bottomAt, _, factors, bottomRecord, facts⟩ :=
    R.toMarkedRealization.copies_scan_completion_factors hlast hp copies cut within lower upper
      atOriginal marked reach frozen earlierRows earlierMarks completed
  obtain ⟨parallelTarget, parallelTrace, parallelComputed, _, parallel⟩ :=
    R.copies_scan_parallel_packet hlast hp copies cut within lower upper atOriginal marked
      reach frozen earlierRows earlierMarks completed
  have sameTrace := Option.some.inj (parallelComputed.symm.trans computed)
  subst parallelTrace
  obtain ⟨entryTarget, entryTrace, _, entryComputed, entryFactors, certificate⟩ :=
    entry.marks oldCursor row mark atOriginal marked
  have entrySame := Option.some.inj (entryComputed.symm.trans computed)
  subst entryTrace
  have seeds := R.copies_scan_seed_history hlast hp copies cut within reach earlierRows
  have bottomMember := List.mem_of_getLast? ((fromRight_two_dropLast trace).symm.trans bottomAt)
  have bottomFacts := facts bottom bottomMember
  have recordWidths : ∀ i ∈ trace.dropLast, ∃ saved,
      (names i, saved) ∈ rec ∧ saved.length = sources.length ∧
      names (i + 1) = names i + sources.length + 1 := by
    intro i member
    have iFacts := facts i member
    obtain ⟨saved, record⟩ := iFacts.2.2.2
    have width := seeds.same_width reach iFacts.1 (iFacts.2.1.trans upper)
      bottomFacts.1 (bottomFacts.2.1.trans upper) (iFacts.2.2.1.trans bottomFacts.2.2.1.symm)
      record bottomRecord
    obtain ⟨old, _, _, atOld, neighbor⟩ := reach.record_neighbors record
    have same : old = i := reach.names_strictMono.injective atOld
    subst old
    exact ⟨saved, record, width, by simpa only [width] using neighbor⟩
  obtain ⟨ownSources, ownRecord, ownWidth, _⟩ := recordWidths mark factors.start_mem
  have ownBefore := reach.forget.record_family_before ownRecord
  have decreasing := (reach.forget.record_source_bounds
    (earlierRows.priorSyntax entry.data.valid entry.data.shapes entry.proper) bottomRecord).1
  let oldOwner : FiniteRowIndex initial := ⟨oldCursor, rowAt_pos atOriginal, rowAt_le_length atOriginal⟩
  let owner : FiniteRowIndex current := ⟨names oldCursor, rowAt_pos atCurrent, rowAt_le_length atCurrent⟩
  apply entry.data.completionHistoryPacket_of_parallel_restrictions E oldOwner owner entryFactors certificate
    decreasing (by dsimp [owner]; omega) parallel
  · exact history oldOwner owner le_rfl (reach.names_strictMono (Nat.lt_succ_self _))
  · intro j bound i member
    obtain ⟨saved, record, width, neighbor⟩ := recordWidths i member
    have beforeOwner := reach.forget.record_family_before record
    have iFacts := facts i member
    have parentPositive := rowAt_pos (getLast_rowAt hlast)
    have oldLength := rowAt_le_length atOriginal
    let oldIndex : FiniteRowIndex initial := ⟨i, by omega, by omega⟩
    let newIndex : FiniteRowIndex current := ⟨names i + j + 1, by omega,
      by have := rowAt_le_length atCurrent; omega⟩
    exact history oldIndex newIndex (by dsimp [oldIndex, newIndex]; omega)
      (by dsimp [oldIndex, newIndex]; omega)

end IBLP.BoundedRealization
