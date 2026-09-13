import IBLP.FrozenGeometry
import IBLP.CompletionGuard

namespace IBLP

theorem Row.properMark_le_q {row : Row} {owner mark q : Nat}
    (valid : row.BasicValid owner) (proper : row.ProperMark mark) (hq : row.q = some q) :
    mark ≤ q := by
  obtain ⟨k, atMark, _, before⟩ := proper
  have atQ : row.columns[row.columns.length - 2]? = some q := by
    simpa only [Row.q, fromRight, show 0 < 2 ∧ 2 ≤ row.columns.length from ⟨by decide, valid.2.1⟩,
      if_true] using hq
  exact Row.column_index_le valid.1 atMark atQ (by omega)

theorem FrozenReach.pending_mem {initial current : Pattern} {rec : Records} {owner mark : Nat}
    {pending : List Nat} (reach : FrozenReach initial rec owner current pending) (member : mark ∈ pending) :
    mark ∈ frozenMarks initial owner := by
  obtain ⟨processed, queue, _⟩ := reach.decomposition
  rw [queue]
  exact List.mem_append_right processed member

theorem FrozenReach.pending_le_q {initial current : Pattern} {rec : Records} {owner mark q : Nat}
    {row : Row} {pending : List Nat} (reach : FrozenReach initial rec owner current pending)
    (valid : BasicValid initial) (proper : ProperMarks initial) (atRow : rowAt initial owner = some row)
    (hq : row.q = some q) (member : mark ∈ pending) : mark ≤ q := by
  have original := reach.pending_mem member
  simp only [frozenMarks, atRow, mem_canonicalColumns, List.mem_filter] at original
  exact Row.properMark_le_q (valid _ _ atRow) (proper row (rowAt_mem atRow) mark original.1) hq

/-- A real completed event at the original penultimate mark, with its
actual nonempty record and exact final q. The remaining count ensures the
event is strictly before the current frozen entrance. -/
def FrozenRaisedQ (initial : Pattern) (rec : Records) (owner oldQ remaining q : Nat) : Prop :=
  ∃ before pending row sources,
    FrozenReach initial rec owner before (oldQ :: pending) ∧ remaining ≤ pending.length ∧
      rowAt before owner = some row ∧ row.q = some oldQ ∧
      completionRecord before rec owner oldQ = some sources ∧ sources ≠ [] ∧
      q = oldQ + sources.length

theorem FrozenRaisedQ.mono {initial : Pattern} {rec : Records} {owner oldQ lower upper q : Nat}
    (origin : FrozenRaisedQ initial rec owner oldQ upper q) (bound : lower ≤ upper) :
    FrozenRaisedQ initial rec owner oldQ lower q := by
  obtain ⟨before, pending, row, sources, reach, length, atRow, hq, guard, nonempty, value⟩ := origin
  exact ⟨before, pending, row, sources, reach, bound.trans length, atRow, hq, guard, nonempty, value⟩

theorem FrozenRaisedQ.growth {initial : Pattern} {rec : Records} {owner oldQ remaining q : Nat}
    (origin : FrozenRaisedQ initial rec owner oldQ remaining q) : oldQ < q := by
  obtain ⟨_, _, _, sources, _, _, _, _, _, nonempty, value⟩ := origin
  cases sources with
  | nil => exact False.elim (nonempty rfl)
  | cons => simp only [List.length_cons] at value; omega

theorem FrozenRaisedQ.original_mark {initial : Pattern} {rec : Records} {owner oldQ remaining q : Nat}
    {row : Row} (origin : FrozenRaisedQ initial rec owner oldQ remaining q)
    (atRow : rowAt initial owner = some row) : oldQ ∈ row.marks := by
  obtain ⟨_, _, _, _, reach, _⟩ := origin
  have member := reach.pending_mem (List.mem_cons_self ..)
  simp only [frozenMarks, atRow, mem_canonicalColumns, List.mem_filter] at member
  exact member.1

/-- During the exact frozen fold q either stays at its entrance value or
has one precisely recoverable growth event at that original value.
All queued marks are old and at most the original q. -/
theorem FrozenReach.q_origin {initial current : Pattern} {rec : Records} {owner oldQ : Nat}
    {original : Row} {pending : List Nat} (reach : FrozenReach initial rec owner current pending)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (atOriginal : rowAt initial owner = some original) (originalQ : original.q = some oldQ)
    (history : FrozenGeometryBefore initial rec owner pending.length) :
    ∃ row q, rowAt current owner = some row ∧ row.q = some q ∧
      (q = oldQ ∨ FrozenRaisedQ initial rec owner oldQ pending.length q) := by
  induction reach with
  | start => exact ⟨original, oldQ, atOriginal, originalQ, Or.inl rfl⟩
  | @next before mark pending previous ih =>
    have earlier : pending.length < (mark :: pending).length := by simp
    have old := previous.invariant valid shapes proper (history.mono earlier.le)
    obtain ⟨row, q, atRow, hq, state⟩ := ih (history.mono earlier.le)
    have markBound := previous.pending_le_q valid proper atOriginal originalQ (List.mem_cons_self ..)
    cases guard : completionRecord before rec owner mark with
    | none =>
      simp only [completeMark, atRow, guard]
      refine ⟨row, q, rfl, hq, ?_⟩
      exact state.imp_right (fun origin => origin.mono earlier.le)
    | some sources =>
      obtain ⟨C⟩ := history before mark pending previous earlier row sources atRow guard
      have qUpdate := C.q_update (old.valid _ _ atRow) (old.shapes row (rowAt_mem atRow)) hq
      have nonempty := (completionRecord_iff.mp guard).choose_spec.choose_spec.2.2.2.1
      simp only [completeMark, atRow, guard]
      refine ⟨completeMarkRow row mark sources, q + if mark = q then sources.length else 0,
        rowAt_set_self atRow, qUpdate, ?_⟩
      rcases state with same | origin
      · subst q
        by_cases atQ : mark = oldQ
        · subst mark
          right
          exact ⟨before, pending, row, sources, previous, le_rfl, atRow, hq, guard, nonempty, by simp⟩
        · left
          simp only [atQ, if_false, Nat.add_zero]
      · obtain ⟨event, tail, eventRow, eventSources, eventReach, count, eventAt, eventQ,
          eventGuard, eventNonempty, value⟩ := origin
        have positive : 0 < eventSources.length := by
          cases eventSources with
          | nil => exact False.elim (eventNonempty rfl)
          | cons => simp
        have different : mark ≠ q := by omega
        simp only [different, if_false, Nat.add_zero]
        exact Or.inr ⟨event, tail, eventRow, eventSources, eventReach, by omega,
          eventAt, eventQ, eventGuard, eventNonempty, value⟩

end IBLP
