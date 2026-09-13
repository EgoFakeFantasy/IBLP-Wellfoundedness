import IBLP.ScanRecords

namespace IBLP

theorem FactorTrace.head {a : Pattern} {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) : rows.head? = some start := by cases h <;> rfl

/-- Parallel factor edges and the actual bottom edge determine the entire
accurate translated history, including an arbitrarily long factor list. -/
theorem FactorTrace.parallel {a b : Pattern} {target start source offset : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows)
    (bottom : ∀ last, rows.getLast? = some last →
      predecessor b (last + offset) = some source ∧ source < last + offset)
    (links : ∀ upper lower, (upper, lower) ∈ rows.zip rows.tail →
      predecessor b (upper + offset) = some (lower + offset)) :
    FactorTrace b source (start + offset) (rows.map (· + offset)) := by
  revert bottom links
  induction h with
  | @single start pred less =>
    intro bottom _
    obtain ⟨edge, bound⟩ := bottom start (by simp)
    exact .single edge bound
  | @cons start next rows pred less inner ih =>
    intro bottom links
    have ends : ∀ last, rows.getLast? = some last →
        predecessor b (last + offset) = some source ∧ source < last + offset := by
      intro last atLast
      exact bottom last (by simpa only [List.getLast?_cons_of_ne_nil inner.nonempty] using atLast)
    obtain ⟨rest, same⟩ := List.head?_eq_some_iff.mp inner.head
    have edge := links start next (by simp [same])
    have inside : ∀ upper lower, (upper, lower) ∈ rows.zip rows.tail →
        predecessor b (upper + offset) = some (lower + offset) := by
      intro upper lower pair
      apply links upper lower
      simpa only [same, List.tail_cons, List.zip_cons_cons] using
        (List.mem_cons_of_mem (start, next) (by simpa only [same, List.tail_cons] using pair))
    exact .cons edge (Nat.add_lt_add_right less offset) (ih ends inside)

/-- Manuscript (6.6), from the exact internal record lists (6.5).
Establishing those lists by record inheritance and component width is a
separate obligation; no first-column check is substituted for it. -/
theorem ScanReach.parallel_factorTrace {initial current : Pattern} {scanStart cursor : Nat} {rec : Records}
    (reach : ScanReach initial scanStart current rec cursor) (history : ScanPriorSyntax initial scanStart cursor)
    {target start bottom j s : Nat} {rows sources : List Nat} (h : FactorTrace current target start rows)
    (atBottom : rows.getLast? = some bottom) (bottomRecord : (bottom, sources) ∈ rec)
    (entry : sources.reverse[j]? = some s)
    (parallelRecords : ∀ upper lower, (upper, lower) ∈ rows.zip rows.tail →
      ∃ ss, (upper, ss) ∈ rec ∧ ss.reverse = (List.range sources.length).map (fun k => lower + k + 1)) :
    FactorTrace current s (start + j + 1) (rows.map (fun i => i + j + 1)) := by
  have jBound : j < sources.length := by simpa only [List.length_reverse] using (List.getElem?_eq_some_iff.mp entry).1
  have result := h.parallel (b := current) (source := s) (offset := j + 1) (by
    intro last atLast
    have same := Option.some.inj (atLast.symm.trans atBottom)
    subst last
    have edge := reach.record_ascending_predecessor history bottomRecord entry
    have below := (reach.record_source_bounds history bottomRecord).2 s
      (List.mem_reverse.mp (List.mem_of_getElem? entry))
    exact ⟨by simpa only [Nat.add_assoc] using edge, by omega⟩) (by
    intro upper lower pair
    obtain ⟨ss, member, exactList⟩ := parallelRecords upper lower pair
    have atPosition : ss.reverse[j]? = some (lower + j + 1) := by simp [exactList, jBound]
    have edge := reach.record_ascending_predecessor history member atPosition
    simpa only [Nat.add_assoc] using edge)
  simpa only [Nat.add_assoc] using result

/-- Saved record factors remain unchanged during any frozen prefix of
the current row; none of their family positions can be that current row. -/
theorem ScanReach.record_factorTrace_frozen {initial current : Pattern} {scanStart cursor : Nat} {rec : Records}
    (reach : ScanReach initial scanStart current rec cursor) (history : ScanPriorSyntax initial scanStart cursor)
    (processed : List Nat) {owner j s : Nat} {sources : List Nat} (member : (owner, sources) ∈ rec)
    (entry : sources.reverse[j]? = some s) :
    FactorTrace (processed.foldl (fun a mark => completeMark a rec cursor mark) current)
      s (owner + j + 1) [owner + j + 1] := by
  have pred := reach.record_ascending_predecessor history member entry
  have jBound : j < sources.length := by simpa only [List.length_reverse] using (List.getElem?_eq_some_iff.mp entry).1
  have before := reach.record_family_before member
  have below := (reach.record_source_bounds history member).2 s
    (List.mem_reverse.mp (List.mem_of_getElem? entry))
  have same := completeMarks_fold_other_row (a := current) (rec := rec) processed
    (by omega : owner + j + 1 ≠ cursor)
  exact .single (by simpa only [predecessor, same] using pred) (by omega)

end IBLP
