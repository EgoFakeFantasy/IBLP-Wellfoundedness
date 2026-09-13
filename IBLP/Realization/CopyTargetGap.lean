import IBLP.FrozenColumns
import IBLP.Realization.CopySeedHistory

namespace IBLP.BoundedRealization
universe u

/-- The literal queued completion has a fresh target packet entirely
before its carrier. Earlier inserted columns cannot enter this packet:
their true family endpoints precede the current old mark. -/
theorem copies_scan_target_gap {stage : ModelStage.{u}} {a copied initial before current : Pattern}
    (R : BoundedRealization stage a) {last row currentRow : Row} {p m k oldCursor mark : Nat}
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
    (completed : completionRecord current rec (names oldCursor) (names mark) = some sources) :
    (∀ x, names mark < x → x ≤ names mark + sources.length → x ∉ currentRow.columns) ∧
      names mark + sources.length < names oldCursor := by
  obtain ⟨next, _, copiedRealization, _, _⟩ := R.toMarkedRealization.rawCopies_realization_exists m copies
  obtain ⟨entry, _, _⟩ := copiedRealization.cut_realization_exists cut
  have entrance := reach.forget.syntax_of_geometry entry.data.valid entry.data.shapes entry.proper earlierRows
  have seeds := R.copies_scan_seed_history hlast hp copies cut within reach earlierRows
  have atBefore := reach.unprocessed_rowAt le_rfl atOriginal
  obtain ⟨saved, record, width, _, fresh⟩ := R.toMarkedRealization.copies_scan_completion_family
    hlast hp copies cut within lower upper atOriginal marked reach frozen earlierRows earlierMarks seeds completed
  refine ⟨?_, ?_⟩
  · intro x above bound member
    have originalColumn := frozen.column_original_above_pending entrance.1 entrance.2.1 entrance.2.2
      earlierMarks atBefore atCurrent (List.mem_cons_self ..) above.le member (by
        intro state earlier todo pastSources previous length order guard
        have queued := previous.pending_mem (List.mem_cons_self ..)
        simp only [frozenMarks, atBefore, mem_canonicalColumns, List.mem_filter] at queued
        obtain ⟨oldMark, oldMarked, image⟩ := List.mem_map.mp queued.1
        subst earlier
        have oldOrder : oldMark < mark := (reach.names_strictMono.lt_iff_lt).mp order
        have prior := earlierMarks.mono (show (names mark :: pending).length ≤
          (names oldMark :: todo).length by simp only [List.length_cons] at *; omega)
        obtain ⟨oldSaved, _, _, nextName, _⟩ := R.toMarkedRealization.copies_scan_completion_family
          hlast hp copies cut within lower upper atOriginal oldMarked reach previous earlierRows prior seeds guard
        have endBound := reach.names_strictMono.monotone (show oldMark + 1 ≤ mark by omega)
        omega)
    obtain ⟨i, _, image⟩ := List.mem_map.mp originalColumn
    exact fresh (x - names mark) (by omega) (by omega) i (by omega)
  · have behind := reach.forget.record_family_before record
    omega

end IBLP.BoundedRealization
