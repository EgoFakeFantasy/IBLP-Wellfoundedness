import IBLP.Realization.CopyRecordShape
import IBLP.TraceAdjacent

namespace IBLP.BoundedRealization
universe u

/-- Manuscript (6.5) for an actual internally checked old factor chain.
All record widths are obtained from the proved seed-history induction;
the exact list contents come from each retained record's labelled birth. -/
theorem copies_scan_internal_records {stage : ModelStage.{u}} {a copied initial current : Pattern}
    (R : BoundedRealization stage a) {last : Row} {p m k oldCursor target start bottom : Nat}
    {rec : Records} {names : Nat → Nat} {rows sources : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) (within : k < m)
    (reach : ScanLabeledReach initial a.length current rec oldCursor names)
    (earlierRows : ScanPriorGeometry initial a.length (names oldCursor))
    (trace : FactorTrace initial target start rows)
    (bounds : ∀ i ∈ rows, a.length + k * (a.length - p) ≤ i ∧
      i < a.length + (k + 1) * (a.length - p))
    (bottomAt : rows.getLast? = some bottom) (bottomRecord : (names bottom, sources) ∈ rec)
    (records : ∀ i ∈ rows, ∃ saved, (names i, saved) ∈ rec) :
    ∀ parent child, (parent, child) ∈ rows.zip rows.tail →
      ∃ saved, (names parent, saved) ∈ rec ∧
        saved.reverse = (List.range sources.length).map (fun j => names child + j + 1) := by
  have seedHistory := R.copies_scan_seed_history hlast hp copies cut within reach earlierRows
  have seeds := trace.blockSeed_eq (fun i member => (bounds i member).1)
  have bottomMember := List.mem_of_getLast? bottomAt
  have bottomBounds := bounds bottom bottomMember
  intro parent child pair
  have parentMember := (List.of_mem_zip pair).1
  have childMember := List.mem_of_mem_tail (List.of_mem_zip pair).2
  have parentBounds := bounds parent parentMember
  have childBounds := bounds child childMember
  obtain ⟨saved, record⟩ := records parent parentMember
  obtain ⟨row, atRow, pred⟩ := Option.bind_eq_some_iff.mp (trace.internal_predecessor pair)
  have exactSources := R.copies_scan_record_shape hlast hp copies cut within parentBounds.2
    childBounds.1 atRow pred reach earlierRows record
  have sameSeed := (seeds parent parentMember).trans (seeds bottom bottomMember).symm
  have width := seedHistory.same_width reach parentBounds.1 parentBounds.2 bottomBounds.1 bottomBounds.2
    sameSeed record bottomRecord
  refine ⟨saved, record, ?_⟩
  calc
    saved.reverse = (descendingPacket (names child) saved.length).reverse := congrArg List.reverse exactSources
    _ = (List.range saved.length).map (fun j => names child + j + 1) := descendingPacket_reverse _ _
    _ = (List.range sources.length).map (fun j => names child + j + 1) := by rw [width]

/-- (6.5) for a literal successful copied/cut frozen completion, with its
accurate entrance trace and actual bottom record recovered from the guard.
No component-width or record-shape premise remains. -/
theorem copies_scan_completion_records {stage : ModelStage.{u}} {a copied initial before current : Pattern}
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
    ∃ target trace bottom, markTrace initial oldCursor mark = some trace ∧
      fromRight trace 2 = some bottom ∧ FactorTrace initial target mark trace.dropLast ∧
      (names bottom, sources) ∈ rec ∧
      (∀ parent child, (parent, child) ∈ trace.dropLast.zip trace.dropLast.tail →
        ∃ saved, (names parent, saved) ∈ rec ∧
          saved.reverse = (List.range sources.length).map (fun j => names child + j + 1)) := by
  obtain ⟨target, trace, bottom, computed, bottomAt, _, factors, bottomRecord, facts⟩ :=
    R.toMarkedRealization.copies_scan_completion_factors hlast hp copies cut within lower upper
      atOriginal marked reach frozen earlierRows earlierMarks completed
  have last : trace.dropLast.getLast? = some bottom := (fromRight_two_dropLast trace).symm.trans bottomAt
  have records := R.copies_scan_internal_records hlast hp copies cut within reach earlierRows factors
    (fun i member => ⟨(facts i member).1, (facts i member).2.1.trans upper⟩)
    last bottomRecord (fun i member => (facts i member).2.2.2)
  exact ⟨target, trace, bottom, computed, bottomAt, factors, bottomRecord, records⟩

end IBLP.BoundedRealization
