import IBLP.Realization.CopyInternalRecords

namespace IBLP.BoundedRealization
universe u

/-- Manuscript (6.6) for the literal successful completion event. Every
packet source has the entire accurate parallel chain in the current
frozen state. Record shape and uniform width are proved internally;
the weak semantic certificate for these chains remains a further step. -/
theorem copies_scan_parallel_packet {stage : ModelStage.{u}} {a copied initial before current : Pattern}
    (R : BoundedRealization stage a) {last row : Row} {p m k oldCursor mark : Nat}
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
    (completed : completionRecord current rec (names oldCursor) (names mark) = some sources) :
    ∃ target trace, markTrace initial oldCursor mark = some trace ∧
      FactorTrace initial target mark trace.dropLast ∧
      (∀ j s, sources.reverse[j]? = some s →
        FactorTrace current s (names mark + j + 1) (trace.dropLast.map (fun i => names i + j + 1))) := by
  obtain ⟨next, _, copiedRealization, _, _⟩ := R.toMarkedRealization.rawCopies_realization_exists m copies
  obtain ⟨entry, _, _⟩ := copiedRealization.cut_realization_exists cut
  obtain ⟨target, trace, bottom, computed, bottomAt, factors, bottomRecord, records⟩ :=
    R.copies_scan_completion_records hlast hp copies cut within lower upper atOriginal marked
      reach frozen earlierRows earlierMarks completed
  have shifted := reach.factorTrace_image_of_geometry entry.data.valid entry.data.shapes entry.proper earlierRows factors
  have bottomLast : trace.dropLast.getLast? = some bottom := (fromRight_two_dropLast trace).symm.trans bottomAt
  have shiftedLast : (trace.dropLast.map names).getLast? = some (names bottom) := by
    rw [List.getLast?_map, bottomLast]
    rfl
  have mappedRecords : ∀ parent child,
      (parent, child) ∈ (trace.dropLast.map names).zip (trace.dropLast.map names).tail →
      ∃ saved, (parent, saved) ∈ rec ∧
        saved.reverse = (List.range sources.length).map (fun j => child + j + 1) := by
    intro parent child pair
    rw [← List.map_tail, List.zip_map] at pair
    obtain ⟨⟨oldParent, oldChild⟩, originalPair, same⟩ := List.mem_map.mp pair
    cases same
    exact records oldParent oldChild originalPair
  have invariants := reach.forget.frozen_invariant_of_geometry frozen entry.data.valid entry.data.shapes
    entry.proper earlierRows earlierMarks
  refine ⟨target, trace, computed, factors, ?_⟩
  intro j s atSource
  have parallel := reach.forget.parallel_factorTrace
    (earlierRows.priorSyntax entry.data.valid entry.data.shapes entry.proper)
    shifted shiftedLast bottomRecord atSource mappedRecords
  simpa only [List.map_map, Function.comp_def] using parallel.of_predecessor_eq invariants.predecessors

end IBLP.BoundedRealization
