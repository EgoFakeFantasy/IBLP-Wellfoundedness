import IBLP.FrozenQ

namespace IBLP

theorem frozenMarks_sorted (a : Pattern) (owner : Nat) :
    (frozenMarks a owner).Pairwise (· < ·) := by
  unfold frozenMarks
  split
  · exact .nil
  · exact canonicalColumns_sorted _

theorem FrozenReach.pending_sorted {initial current : Pattern} {rec : Records} {owner : Nat}
    {pending : List Nat} (reach : FrozenReach initial rec owner current pending) :
    pending.Pairwise (· < ·) := by
  obtain ⟨processed, queue, _⟩ := reach.decomposition
  have sorted := frozenMarks_sorted initial owner
  rw [queue, List.pairwise_append] at sorted
  exact sorted.2.1

theorem completeMarkRow_column_mem {row : Row} {mark x : Nat} {sources : List Nat} :
    x ∈ (completeMarkRow row mark sources).columns ↔
      x ∈ row.columns ∨ x ∈ sources ∨ mark < x ∧ x ≤ mark + sources.length := by
  simp only [completeMarkRow, mem_canonicalColumns, List.mem_append, List.mem_map,
    List.mem_range]
  constructor
  · rintro ((old | source) | ⟨j, bound, value⟩)
    · exact Or.inl old
    · exact Or.inr (Or.inl source)
    · exact Or.inr (Or.inr (by omega))
  · rintro (old | source | ⟨lower, upper⟩)
    · exact Or.inl (Or.inl old)
    · exact Or.inl (Or.inr source)
    · exact Or.inr ⟨x - (mark + 1), by omega, by omega⟩

/-- Every new column in an actual frozen prefix comes from a real earlier
completion. Its queued mark is strictly below every still-pending mark.
No geometry or semantic correctness is assumed here. -/
theorem FrozenReach.column_origin {initial current : Pattern} {rec : Records} {owner x : Nat}
    {original row : Row} {pending : List Nat}
    (reach : FrozenReach initial rec owner current pending)
    (atOriginal : rowAt initial owner = some original) (atRow : rowAt current owner = some row)
    (member : x ∈ row.columns) :
    x ∈ original.columns ∨ ∃ before earlier todo past sources,
      FrozenReach initial rec owner before (earlier :: todo) ∧ pending.length ≤ todo.length ∧
      (∀ mark ∈ pending, earlier < mark) ∧ rowAt before owner = some past ∧
      completionRecord before rec owner earlier = some sources ∧
      (x ∈ sources ∨ earlier < x ∧ x ≤ earlier + sources.length) := by
  induction reach generalizing row with
  | start =>
    have same : original = row := Option.some.inj (atOriginal.symm.trans atRow)
    exact Or.inl (by simpa only [same] using member)
  | @next before earlier todo previous ih =>
    have lift : ∀ past, rowAt before owner = some past → x ∈ past.columns →
        x ∈ original.columns ∨ ∃ state mark rest old sources,
          FrozenReach initial rec owner state (mark :: rest) ∧ todo.length ≤ rest.length ∧
          (∀ next ∈ todo, mark < next) ∧ rowAt state owner = some old ∧
          completionRecord state rec owner mark = some sources ∧
          (x ∈ sources ∨ mark < x ∧ x ≤ mark + sources.length) := by
      intro past atPast inPast
      rcases ih atPast inPast with old | ⟨state, mark, rest, old, ss, born, length, order, atOld, guard, added⟩
      · exact Or.inl old
      · exact Or.inr ⟨state, mark, rest, old, ss, born, by simpa using Nat.le_trans (by simp) length,
          fun next hnext => order next (List.mem_cons_of_mem _ hnext), atOld, guard, added⟩
    unfold completeMark at atRow
    split at atRow
    · rename_i past sources atPast guard
      rw [rowAt_set_self atPast] at atRow
      cases Option.some.inj atRow
      rcases completeMarkRow_column_mem.mp member with old | added
      · exact lift past atPast old
      · exact Or.inr ⟨before, earlier, todo, past, sources, previous, le_rfl,
          (List.pairwise_cons.mp previous.pending_sorted).1, atPast, guard, added⟩
    · exact lift row atRow member

/-- Once earlier target packets end below a still-pending mark, every
column at or above that mark is an unchanged entrance column. Earlier
source packets are below their marks by the earlier local geometry. -/
theorem FrozenReach.column_original_above_pending {initial current : Pattern} {rec : Records}
    {owner mark x : Nat} {original row : Row} {pending : List Nat}
    (reach : FrozenReach initial rec owner current pending)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : FrozenGeometryBefore initial rec owner pending.length)
    (atOriginal : rowAt initial owner = some original) (atRow : rowAt current owner = some row)
    (queued : mark ∈ pending) (above : mark ≤ x) (member : x ∈ row.columns)
    (targetBound : ∀ before earlier todo sources,
      FrozenReach initial rec owner before (earlier :: todo) → pending.length ≤ todo.length →
      earlier < mark → completionRecord before rec owner earlier = some sources →
      earlier + sources.length < mark) : x ∈ original.columns := by
  rcases reach.column_origin atOriginal atRow member with old |
    ⟨before, earlier, todo, past, sources, previous, length, order, atPast, guard, added⟩
  · exact old
  · have earlierLt := order mark queued
    have time : pending.length < (earlier :: todo).length := by simp only [List.length_cons]; omega
    obtain ⟨C⟩ := history before earlier todo previous time past sources atPast guard
    have old := previous.invariant valid shapes proper (history.mono time.le)
    rcases added with source | target
    · have bound := C.sources_below_mark (old.valid _ _ atPast).1
        (old.shapes past (rowAt_mem atPast)) x source
      omega
    · have bound := targetBound before earlier todo sources previous length earlierLt guard
      omega

/-- A proper entrance mark remains proper after every strictly earlier
geometrically justified event, whether or not it is the next queued mark. -/
theorem FrozenReach.proper_mark {initial current : Pattern} {rec : Records} {owner mark : Nat}
    {original row : Row} {pending : List Nat}
    (reach : FrozenReach initial rec owner current pending)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : FrozenGeometryBefore initial rec owner pending.length)
    (atOriginal : rowAt initial owner = some original) (atRow : rowAt current owner = some row)
    (marked : original.ProperMark mark) : row.ProperMark mark := by
  induction reach generalizing row with
  | start =>
    have same := Option.some.inj (atOriginal.symm.trans atRow)
    simpa only [same] using marked
  | @next before earlier todo previous ih =>
    have time : todo.length < (earlier :: todo).length := by simp
    have old := previous.invariant valid shapes proper (history.mono time.le)
    unfold completeMark at atRow
    split at atRow
    · rename_i past sources atPast guard
      rw [rowAt_set_self atPast] at atRow
      cases Option.some.inj atRow
      obtain ⟨C⟩ := history before earlier todo previous time past sources atPast guard
      exact C.old_proper (old.valid _ _ atPast) (old.shapes past (rowAt_mem atPast))
        (ih (history.mono time.le) atPast)
    · exact ih (history.mono time.le) atRow

end IBLP
