import IBLP.ScanTermination

namespace IBLP

/-- Actual scan entrances, with the manuscript's arbitrary initial cursor
and empty initial record. Each transition skips the whole new family. -/
inductive ScanReach (initial : Pattern) (start : Nat) : Pattern → Records → Nat → Prop
  | start : ScanReach initial start initial [] start
  | next {a b rec r sources} : ScanReach initial start a rec r → r ≤ a.length →
      native (completeFrozenMarks a rec r) r = some (b, sources) →
      ScanReach initial start b (if sources.isEmpty then rec else (r, sources) :: rec)
        (r + sources.length + 1)

theorem ScanReach.cursor_ge_start {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) : start ≤ cursor := by
  induction reach with
  | start => rfl
  | next _ _ _ ih => omega

theorem ScanReach.records_nonempty {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) : ∀ entry ∈ rec, entry.2 ≠ [] := by
  induction reach with
  | start => simp
  | @next before after history owner sources previous bound run ih =>
    by_cases empty : sources = []
    · simpa only [empty, List.isEmpty_nil, if_true] using ih
    · simp only [List.isEmpty_iff, empty, if_false]
      intro entry member
      rcases List.mem_cons.mp member with same | old
      · subst entry; exact empty
      · exact ih entry old

/-- Stored owners and their full families are strictly behind the cursor.
This fact uses the exact program, without semantic or saturation premises. -/
theorem ScanReach.record_family_before {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) {owner : Nat} {sources : List Nat}
    (member : (owner, sources) ∈ rec) : owner + sources.length < cursor := by
  induction reach with
  | start => simp at member
  | @next before after history base ss previous bound run ih =>
    by_cases empty : ss = []
    · simp only [empty, List.isEmpty_nil, if_true] at member
      have previousBound := ih member
      omega
    · simp only [List.isEmpty_iff, empty, if_false] at member
      rcases List.mem_cons.mp member with same | old
      · cases same; omega
      · have previousBound := ih old; omega

theorem ScanReach.record_owners_distinct {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) : (rec.map Prod.fst).Nodup := by
  induction reach with
  | start => simp
  | @next before after history owner sources previous bound run ih =>
    by_cases empty : sources = []
    · simpa only [empty, List.isEmpty_nil, if_true] using ih
    · simp only [List.isEmpty_iff, empty, if_false, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro member
      obtain ⟨⟨oldOwner, oldSources⟩, oldMember, same⟩ := List.mem_map.mp member
      have behind := previous.record_family_before oldMember
      change oldOwner = owner at same
      omega

theorem ScanRun.reaches {initial current result : Pattern} {start cursor : Nat} {rec : Records}
    (run : ScanRun current rec cursor result) : ScanReach initial start current rec cursor →
      ∃ finalRec finalCursor, ScanReach initial start result finalRec finalCursor ∧ result.length < finalCursor := by
  induction run with
  | done bound => intro reach; exact ⟨_, _, reach, bound⟩
  | next bound step rest ih =>
    intro reach
    exact ih (.next reach bound step)

theorem scan_reaches_end {initial result : Pattern} {start : Nat}
    (run : scan initial start = some result) :
    ∃ rec cursor, ScanReach initial start result rec cursor ∧ result.length < cursor :=
  (scan_iff.mp run).reaches .start

end IBLP
