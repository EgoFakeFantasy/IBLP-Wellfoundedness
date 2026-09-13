import IBLP.ScanQOrigin

namespace IBLP

/-- A processed entrance row either has no inserted family, or its
nonempty family is actually present in the current record table. -/
theorem ScanLabeledReach.record_or_adjacent {initial current : Pattern}
    {start oldCursor i : Nat} {rec : Records} {names : Nat → Nat}
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (scanned : start ≤ i) (processed : i < oldCursor) :
    names (i + 1) = names i + 1 ∨ ∃ sources, (names i, sources) ∈ rec ∧
      names (i + 1) = names i + sources.length + 1 := by
  induction reach with
  | start => omega
  | @next before after records old name sources previous bound run ih =>
    by_cases last : i = old
    · subst i
      have atOwner := previous.processed_names_fixed (Nat.le_refl old) (h := sources.length)
      by_cases empty : sources = []
      · left
        rw [previous.next_cursor, atOwner, empty]
        simp
      · right
        refine ⟨sources, ?_, ?_⟩
        · simp only [List.isEmpty_iff, empty, if_false, atOwner, List.mem_cons_self]
        · rw [previous.next_cursor, atOwner]
    · have beforeOld : i < old := by omega
      have fixedI := previous.processed_names_fixed beforeOld.le (h := sources.length)
      have fixedNext := previous.processed_names_fixed (by omega : i + 1 ≤ old) (h := sources.length)
      rcases ih (by omega) with adjacent | ⟨saved, member, neighbors⟩
      · left
        rwa [fixedNext, fixedI]
      · right
        refine ⟨saved, ?_, ?_⟩
        · rw [fixedI]
          by_cases empty : sources = []
          · simpa only [empty, List.isEmpty_nil, if_true] using member
          · simp only [List.isEmpty_iff, empty, if_false]
            exact List.mem_cons_of_mem _ member
        · rwa [fixedNext, fixedI]

theorem native_empty_base_row {a b : Pattern} {owner : Nat} {row : Row}
    (run : native a owner = some (b, [])) (atRow : rowAt a owner = some row) :
    rowAt b owner = some row := by
  simpa only [Nat.add_zero, List.getElem?_cons_zero] using
    native_family_rowAt atRow run (show nativeBlock row owner [] = some [row] from rfl)
      (show 0 < [row].length by simp)

/-- If a processed old row has no saved record, its original endpoint
survives under the current labels. Only earlier completion geometry is used. -/
theorem ScanLabeledReach.no_record_endpoint {initial current : Pattern}
    {start oldCursor i endpoint : Nat} {rec : Records} {names : Nat → Nat} {row : Row}
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : ScanPriorGeometry initial start (names oldCursor))
    (scanned : start ≤ i) (processed : i < oldCursor)
    (atOriginal : rowAt initial i = some row) (originalE : row.e = some endpoint)
    (absent : ∀ sources, (names i, sources) ∉ rec) :
    (rowAt current (names i)).bind Row.e = some (names endpoint) := by
  have adjacent : names (i + 1) = names i + 1 := by
    rcases reach.record_or_adjacent scanned processed with equal | ⟨sources, member, _⟩
    · exact equal
    · exact False.elim (absent sources member)
  obtain ⟨before, records, after, sources, birthNames, event, run, labels, neighbors, unchanged⟩ :=
    reach.processed_step scanned processed
  have empty : sources = [] := by
    cases sources with
    | nil => rfl
    | cons => simp only [List.length_cons] at neighbors; omega
  subst sources
  have atI := labels i (Nat.le_refl _)
  have earlier : birthNames i < names oldCursor := by rw [atI]; exact reach.names_strictMono processed
  have atBirth := event.unprocessed_rowAt (Nat.le_refl _) atOriginal
  have eBirth : (Row.mk (row.columns.map birthNames) row.step (row.marks.map birthNames)).e =
      some (birthNames endpoint) := by
    change fromRight (row.columns.map birthNames) row.step = _
    rw [fromRight_map]
    change row.e.map birthNames = _
    rw [originalE]
    rfl
  have birthSyntax := event.forget.syntax_of_geometry valid shapes proper (history.mono earlier.le)
  have marked := completeFrozenMarks_invariant birthSyntax.1 birthSyntax.2.1 birthSyntax.2.2
    (history before records (birthNames i) event.forget earlier)
  have markedE : (rowAt (completeFrozenMarks before records (birthNames i)) (birthNames i)).bind Row.e =
      some (birthNames endpoint) := by
    rw [marked.endpoints, atBirth]
    exact eBirth
  obtain ⟨mid, atMid, midE⟩ := Option.bind_eq_some_iff.mp markedE
  have endpointBound : endpoint ≤ i := fromRight_le_last (valid _ _ atOriginal).1
    (valid _ _ atOriginal).2.2.1 (Row.step_pos (shapes row (rowAt_mem atOriginal))) originalE
  have afterE : (rowAt after (birthNames i)).bind Row.e = some (birthNames endpoint) := by
    rw [native_empty_base_row run atMid]
    exact midE
  rw [atI, labels endpoint endpointBound] at afterE
  rw [unchanged (names i) (by simp)]
  exact afterE

/-- An old row whose endpoint is the first new point of an actual saved
family must itself have a nonempty saved record. This is the local step
used to climb an internally checked old factor chain. -/
theorem ScanLabeledReach.record_of_endpoint_target {initial current : Pattern}
    {start oldCursor parent child : Nat} {rec : Records} {names : Nat → Nat} {row : Row}
    {saved : List Nat} (reach : ScanLabeledReach initial start current rec oldCursor names)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : ScanPriorGeometry initial start (names oldCursor))
    (scanned : start ≤ parent) (processed : parent < oldCursor)
    (atOriginal : rowAt initial parent = some row) (childRecord : (names child, saved) ∈ rec)
    (endpoint : (rowAt current (names parent)).bind Row.e = some (names child + 1)) :
    ∃ sources, (names parent, sources) ∈ rec := by
  by_contra noRecord
  have absent : ∀ sources, (names parent, sources) ∉ rec := by simpa only [not_exists] using noRecord
  have shape := shapes row (rowAt_mem atOriginal)
  obtain ⟨oldE, atE⟩ := fromRight_exists (xs := row.columns) (Row.step_pos shape) (Row.step_lt_length shape).le
  have retained := reach.no_record_endpoint valid shapes proper history scanned processed atOriginal atE absent
  have equal := Option.some.inj (retained.symm.trans endpoint)
  have nonempty := reach.forget.records_nonempty (names child, saved) childRecord
  have positive : 1 ≤ saved.length := by
    cases saved with
    | nil => exact False.elim (nonempty rfl)
    | cons => simp
  exact reach.record_family_not_old childRecord (by decide : 0 < 1) positive oldE equal

end IBLP
