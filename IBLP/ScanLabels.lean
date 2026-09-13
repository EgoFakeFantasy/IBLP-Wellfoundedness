import IBLP.ScanReach
import IBLP.NativeTraceShift

namespace IBLP

/-- The actual original scan, with entrance labels retained for old
vertices. New native family points are never assigned entrance labels.
`oldCursor` advances once per processed old row; `names` tracks all insertions. -/
inductive ScanLabeledReach (initial : Pattern) (start : Nat) :
    Pattern → Records → Nat → (Nat → Nat) → Prop
  | start : ScanLabeledReach initial start initial [] start id
  | next {a b rec oldCursor names sources} :
      ScanLabeledReach initial start a rec oldCursor names → names oldCursor ≤ a.length →
      native (completeFrozenMarks a rec (names oldCursor)) (names oldCursor) = some (b, sources) →
      ScanLabeledReach initial start b
        (if sources.isEmpty then rec else (names oldCursor, sources) :: rec)
        (oldCursor + 1) (shiftAfter (names oldCursor) sources.length ∘ names)

theorem ScanLabeledReach.names_strictMono {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names) :
    StrictMono names := by
  induction reach with
  | start => exact strictMono_id
  | next _ _ _ ih => exact (shiftAfter_strictMono _ _).comp ih

theorem ScanLabeledReach.oldCursor_ge_start {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names) :
    start ≤ oldCursor := by
  induction reach with
  | start => rfl
  | next _ _ _ ih => omega

/-- Unprocessed entrance labels remain consecutive. Written additively
to avoid any ambiguity from truncated subtraction of natural labels. -/
theorem ScanLabeledReach.suffix_balance {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names)
    (i : Nat) (after : oldCursor ≤ i) : names i + oldCursor = names oldCursor + i := by
  induction reach generalizing i with
  | start => simp only [id_eq]; omega
  | @next before result history old name sources previous bound run ih =>
    have atI := ih i (by omega : old ≤ i)
    have atNext := ih (old + 1) (by omega)
    have above := previous.names_strictMono (by omega : old < i)
    have aboveNext := previous.names_strictMono (Nat.lt_succ_self old)
    simp only [Function.comp_apply, shiftAfter, if_pos above, if_pos aboveNext]
    omega

theorem ScanLabeledReach.next_cursor {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names)
    (h : Nat) :
    (shiftAfter (names oldCursor) h ∘ names) (oldCursor + 1) = names oldCursor + h + 1 := by
  have balance := reach.suffix_balance (oldCursor + 1) (Nat.le_succ oldCursor)
  have above := reach.names_strictMono (Nat.lt_succ_self oldCursor)
  simp only [Function.comp_apply, shiftAfter, if_pos above]
  omega

/-- Forgetting labels recovers the literal scan, including the exact cursor
that skips a native family. No different scan schedule is introduced. -/
theorem ScanLabeledReach.forget {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names) :
    ScanReach initial start current rec (names oldCursor) := by
  induction reach with
  | start => exact .start
  | @next before result history old name sources previous bound run ih =>
    rw [previous.next_cursor]
    exact .next ih bound run

/-- Every actual scan entrance has entrance labels, rather than this
being an extra hypothesis about specially selected executions. -/
theorem ScanReach.labeled {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) :
    ∃ oldCursor names, ScanLabeledReach initial start current rec oldCursor names ∧ names oldCursor = cursor := by
  induction reach with
  | start => exact ⟨start, id, .start, rfl⟩
  | @next before result history owner sources previous bound run ih =>
    obtain ⟨old, name, labeled, ownerEq⟩ := ih
    have run' : native (completeFrozenMarks before history (name old)) (name old) = some (result, sources) := by
      simpa only [ownerEq] using run
    have next := ScanLabeledReach.next labeled (by simpa only [ownerEq] using bound) run'
    refine ⟨old + 1, shiftAfter (name old) sources.length ∘ name, ?_, ?_⟩
    · simpa only [ownerEq] using next
    · rw [labeled.next_cursor, ownerEq]

/-- Insertions account for the whole difference between current and
entrance row numbers; each event consumes exactly one old vertex. -/
theorem ScanLabeledReach.length_balance {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names) :
    current.length + oldCursor = initial.length + names oldCursor := by
  induction reach with
  | start => rfl
  | @next before result history old name sources previous bound run ih =>
    have length := native_length run
    rw [completeFrozenMarks_length] at length
    rw [previous.next_cursor]
    omega

theorem ScanLabeledReach.finished_iff {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names) :
    current.length < names oldCursor ↔ initial.length < oldCursor := by
  have balance := reach.length_balance
  omega

theorem ScanLabeledReach.prefix_names {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names)
    {i : Nat} (before : i < start) : names i = i := by
  induction reach with
  | start => rfl
  | @next a b history old name sources previous bound run ih =>
    have ordered := previous.names_strictMono.monotone (before.le.trans previous.oldCursor_ge_start)
    simp only [Function.comp_apply, shiftAfter]
    rw [if_neg (Nat.not_lt.mpr ordered), ih]

/-- Processing an old vertex fixes its own label and every earlier label. -/
theorem ScanLabeledReach.processed_names_fixed {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names)
    {i h : Nat} (before : i ≤ oldCursor) :
    (shiftAfter (names oldCursor) h ∘ names) i = names i := by
  have ordered := reach.names_strictMono.monotone before
  simp only [Function.comp_apply, shiftAfter, if_neg (Nat.not_lt.mpr ordered)]

/-- Every new family point lies strictly between consecutive old labels.
In particular a numerical successor in that family is not an old vertex. -/
theorem shiftAfter_family_not_old {owner h point : Nat}
    (lower : owner < point) (upper : point ≤ owner + h) (old : Nat) :
    shiftAfter owner h old ≠ point := by
  unfold shiftAfter
  split <;> omega

theorem ScanLabeledReach.family_not_old {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (_reach : ScanLabeledReach initial start current rec oldCursor names)
    {h j : Nat} (positive : 0 < j) (within : j ≤ h) (old : Nat) :
    (shiftAfter (names oldCursor) h ∘ names) old ≠ names oldCursor + j :=
  shiftAfter_family_not_old (by omega) (by omega) (names old)

/-- A saved family remains between its owner's entrance label and the
next old label after every later event, including processing that next row. -/
theorem ScanLabeledReach.record_neighbors {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names)
    {owner : Nat} {sources : List Nat} (member : (owner, sources) ∈ rec) :
    ∃ old, start ≤ old ∧ old < oldCursor ∧ names old = owner ∧
      names (old + 1) = owner + sources.length + 1 := by
  induction reach with
  | start => simp at member
  | @next before result history base name ss previous bound run ih =>
    have retain (oldMember : (owner, sources) ∈ history) :
        ∃ old, start ≤ old ∧ old < base + 1 ∧
          (shiftAfter (name base) ss.length ∘ name) old = owner ∧
          (shiftAfter (name base) ss.length ∘ name) (old + 1) = owner + sources.length + 1 := by
      obtain ⟨old, lower, upper, atOwner, atNext⟩ := ih oldMember
      refine ⟨old, lower, by omega, ?_, ?_⟩
      · rw [previous.processed_names_fixed (by omega : old ≤ base), atOwner]
      · rw [previous.processed_names_fixed (by omega : old + 1 ≤ base), atNext]
    by_cases empty : ss = []
    · simp only [empty, List.isEmpty_nil, if_true] at member
      exact retain member
    · simp only [List.isEmpty_iff, empty, if_false] at member
      rcases List.mem_cons.mp member with equal | oldMember
      · cases equal
        exact ⟨base, previous.oldCursor_ge_start, Nat.lt_succ_self _,
          previous.processed_names_fixed le_rfl, previous.next_cursor _⟩
      · exact retain oldMember

/-- The numerical points of every saved native family are absent from
the entire current image of entrance labels. -/
theorem ScanLabeledReach.record_family_not_old {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names)
    {owner j : Nat} {sources : List Nat} (member : (owner, sources) ∈ rec)
    (positive : 0 < j) (within : j ≤ sources.length) (i : Nat) : names i ≠ owner + j := by
  obtain ⟨old, _, _, atOwner, atNext⟩ := reach.record_neighbors member
  by_cases before : i ≤ old
  · have ordered := reach.names_strictMono.monotone before
    rw [atOwner] at ordered
    omega
  · have ordered := reach.names_strictMono.monotone (show old + 1 ≤ i by omega)
    rw [atNext] at ordered
    omega

/-- An entrance vertex before the scan start can never acquire a record
in this round, even after arbitrarily many native insertions. -/
theorem ScanLabeledReach.no_record_before_start {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names)
    {i : Nat} (before : i < start) (sources : List Nat) : (names i, sources) ∉ rec := by
  intro member
  obtain ⟨old, lower, _, atOwner, _⟩ := reach.record_neighbors member
  have ordered := reach.names_strictMono (before.trans_le lower)
  rw [atOwner] at ordered
  exact (Nat.lt_irrefl _) ordered

end IBLP
