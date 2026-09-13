import IBLP.ScanEmptyRecord
import IBLP.ParallelTrace

namespace IBLP

/-- Starting with the bottom's actual record, climb all internal old
arrows whose current endpoint is the next factor's first family point. -/
theorem ScanLabeledReach.factor_records {initial current : Pattern}
    {scanStart oldCursor target start : Nat} {rec : Records} {names : Nat → Nat} {rows : List Nat}
    (reach : ScanLabeledReach initial scanStart current rec oldCursor names)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : ScanPriorGeometry initial scanStart (names oldCursor))
    (trace : FactorTrace initial target start rows)
    (bounds : ∀ i ∈ rows, scanStart ≤ i ∧ i < oldCursor)
    (bottom : ∀ last, rows.getLast? = some last → ∃ sources, (names last, sources) ∈ rec)
    (endpoints : ∀ parent child, (parent, child) ∈ rows.zip rows.tail →
      (rowAt current (names parent)).bind Row.e = some (names child + 1)) :
    ∀ i ∈ rows, ∃ sources, (names i, sources) ∈ rec := by
  revert bounds bottom endpoints
  induction trace with
  | @single start pred less =>
    intro _ bottom _ i member
    have same := List.mem_singleton.mp member
    subst i
    exact bottom start (by simp)
  | @cons start next rows pred less inner ih =>
    intro bounds bottom endpoints
    have innerBounds : ∀ i ∈ rows, scanStart ≤ i ∧ i < oldCursor :=
      fun i member => bounds i (List.mem_cons_of_mem _ member)
    have innerBottom : ∀ last, rows.getLast? = some last → ∃ sources, (names last, sources) ∈ rec := by
      intro last atLast
      apply bottom last
      simpa only [List.getLast?_cons_of_ne_nil inner.nonempty] using atLast
    obtain ⟨rest, same⟩ := List.head?_eq_some_iff.mp inner.head
    have firstEndpoint := endpoints start next (by simp [same])
    have innerEndpoints : ∀ parent child, (parent, child) ∈ rows.zip rows.tail →
        (rowAt current (names parent)).bind Row.e = some (names child + 1) := by
      intro parent child pair
      apply endpoints parent child
      simpa only [same, List.tail_cons, List.zip_cons_cons] using
        List.mem_cons_of_mem (start, next) (by simpa only [same, List.tail_cons] using pair)
    have innerRecords := ih innerBounds innerBottom innerEndpoints
    obtain ⟨childSources, childRecord⟩ := innerRecords next inner.start_mem
    obtain ⟨row, atRow, _⟩ := Option.bind_eq_some_iff.mp pred
    have startBounds := bounds start (List.mem_cons_self ..)
    have startRecord := reach.record_of_endpoint_target valid shapes proper history
      startBounds.1 startBounds.2 atRow childRecord firstEndpoint
    intro i member
    rcases List.mem_cons.mp member with same | later
    · subst i; exact startRecord
    · exact innerRecords i later

/-- The literal internal check at an actual frozen prefix supplies those
endpoint equations. Every old nonterminal factor then has an actual
nonempty record; the terminal paired source is excluded. -/
theorem ScanLabeledReach.internalCheck_factor_records {initial before current : Pattern}
    {scanStart oldCursor target start : Nat} {rec : Records} {names : Nat → Nat}
    {rows pending : List Nat}
    (reach : ScanLabeledReach initial scanStart before rec oldCursor names)
    (frozen : FrozenReach before rec (names oldCursor) current pending)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (earlierRows : ScanPriorGeometry initial scanStart (names oldCursor))
    (earlierMarks : FrozenGeometryBefore before rec (names oldCursor) pending.length)
    (trace : FactorTrace initial target start rows)
    (bounds : ∀ i ∈ rows, scanStart ≤ i ∧ i < oldCursor)
    (bottom : ∀ last, rows.getLast? = some last → ∃ sources, (names last, sources) ∈ rec)
    (guard : internalCheck current (rows.map names ++ [names target]) = true) :
    ∀ i ∈ rows, ∃ sources, (names i, sources) ∈ rec := by
  have invariants := reach.forget.frozen_invariant_of_geometry frozen valid shapes proper earlierRows earlierMarks
  have shifted := reach.factorTrace_image_of_geometry valid shapes proper earlierRows trace
  have actual := (shifted.of_predecessor_eq invariants.predecessors).toTrace
  have checked := internalCheck_endpoints invariants.valid invariants.shapes actual guard
  apply reach.factor_records valid shapes proper earlierRows trace bounds bottom
  intro parent child pair
  have mappedPair : (names parent, names child) ∈ (rows.map names).zip (rows.map names).tail := by
    rw [← List.map_tail, List.zip_map]
    exact List.mem_map.mpr ⟨(parent, child), pair, rfl⟩
  have actualPair : (names parent, names child) ∈
      (rows.map names ++ [names target]).dropLast.zip (rows.map names ++ [names target]).dropLast.tail := by
    simpa only [List.dropLast_concat] using mappedPair
  obtain ⟨row, atRow, _, endpoint⟩ := checked (names parent) (names child) actualPair
  have parentMember : parent ∈ rows := List.of_mem_zip pair |>.1
  have behind := reach.names_strictMono (bounds parent parentMember).2
  have atBefore := (frozen.rowAt_other (by omega : names parent ≠ names oldCursor)).symm.trans atRow
  simp only [atBefore, Option.bind_some, endpoint]

end IBLP
