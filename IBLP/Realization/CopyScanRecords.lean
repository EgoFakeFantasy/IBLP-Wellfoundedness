import IBLP.Realization.CopyScanEntry
import IBLP.Realization.CutRealized
import IBLP.ScanFactorRecords
import IBLP.TraceBottom
import IBLP.BlockSeed

namespace IBLP.MarkedRealization
universe u

/-- At an actual successful frozen completion in a copied block, recover
the entrance old trace. Every nonterminal factor lies in that same block
and has an actual nonempty saved record. No component-width or current
event geometry is assumed in this conclusion. -/
theorem copies_scan_completion_factors {stage : ModelStage.{u}} {a copied initial before current : Pattern}
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
    (completed : completionRecord current rec (names oldCursor) (names mark) = some sources) :
    ∃ target trace bottom, markTrace initial oldCursor mark = some trace ∧
      fromRight trace 2 = some bottom ∧ a.length ≤ bottom ∧
      FactorTrace initial target mark trace.dropLast ∧ (names bottom, sources) ∈ rec ∧
      (∀ i ∈ trace.dropLast, a.length + k * (a.length - p) ≤ i ∧ i < oldCursor ∧
        blockSeed initial (a.length + k * (a.length - p)) i =
          blockSeed initial (a.length + k * (a.length - p)) mark ∧
        ∃ saved, (names i, saved) ∈ rec) := by
  obtain ⟨next, _, copiedRealization, _, _⟩ := R.rawCopies_realization_exists m copies
  obtain ⟨entry, _, _⟩ := copiedRealization.cut_realization_exists cut
  obtain ⟨target, trace, paired, computed, factors, _⟩ := entry.marks oldCursor row mark atOriginal marked
  obtain ⟨currentTrace, currentBottom, currentComputed, currentAt, lookup, _, checked⟩ :=
    completionRecord_iff.mp completed
  have retained := reach.frozen_markTrace frozen entry.data.valid entry.data.shapes entry.proper
    earlierRows earlierMarks computed
  have traceSame : currentTrace = trace.map names := Option.some.inj (currentComputed.symm.trans retained)
  rw [traceSame, fromRight_map] at currentAt
  obtain ⟨bottom, bottomAt, bottomSame⟩ := Option.map_eq_some_iff.mp currentAt
  have bottomRecord : (names bottom, sources) ∈ rec := by rw [bottomSame]; exact recordAt_mem lookup
  have active : a.length ≤ bottom := by
    by_contra outside
    exact reach.no_record_before_start (by omega : bottom < a.length) sources bottomRecord
  have blockBounds := R.copies_cut_block_active_factors hlast hp copies cut within lower upper
    atOriginal marked computed bottomAt active
  have traceShape : trace = trace.dropLast ++ [target] :=
    (markTrace_spec atOriginal paired computed).2.2.unique factors.toTrace
  have actualCheck : internalCheck current (trace.dropLast.map names ++ [names target]) = true := by
    rw [traceSame] at checked
    conv at checked => lhs; arg 2; rw [traceShape]
    simpa only [List.map_append, List.map_cons, List.map_nil] using checked
  have allRecords := reach.internalCheck_factor_records frozen entry.data.valid entry.data.shapes entry.proper
    earlierRows earlierMarks factors
    (fun i member => ⟨by have := (blockBounds i member).1; omega, (blockBounds i member).2⟩)
    (by
      intro last atLast
      have bottomLast : trace.dropLast.getLast? = some bottom := (fromRight_two_dropLast trace).symm.trans bottomAt
      have same := Option.some.inj (atLast.symm.trans bottomLast)
      subst last
      exact ⟨sources, bottomRecord⟩)
    actualCheck
  have sameSeed := factors.blockSeed_eq (fun i member => (blockBounds i member).1)
  exact ⟨target, trace, bottom, computed, bottomAt, active, factors, bottomRecord,
    fun i member => ⟨(blockBounds i member).1, (blockBounds i member).2,
      sameSeed i member, allRecords i member⟩⟩

end IBLP.MarkedRealization
