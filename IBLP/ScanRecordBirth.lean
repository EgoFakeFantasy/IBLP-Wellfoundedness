import IBLP.ScanPrefix

namespace IBLP

/-- A retained record comes from an actual earlier native event. Every
row through the end of that event's family is still exactly its birth row.
No legality or semantic history premise is needed for this provenance. -/
theorem ScanReach.record_birth {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) {owner : Nat} {sources : List Nat}
    (member : (owner, sources) ∈ rec) :
    ∃ before history after, ScanReach initial start before history owner ∧ owner ≤ before.length ∧
      native (completeFrozenMarks before history owner) owner = some (after, sources) ∧
      ∀ i, i ≤ owner + sources.length → rowAt current i = rowAt after i := by
  induction reach with
  | start => simp at member
  | @next before after history base ss previous bound run ih =>
    have inherit : (owner, sources) ∈ history →
        ∃ birth birthHistory birthAfter, ScanReach initial start birth birthHistory owner ∧ owner ≤ birth.length ∧
          native (completeFrozenMarks birth birthHistory owner) owner = some (birthAfter, sources) ∧
          ∀ i, i ≤ owner + sources.length → rowAt after i = rowAt birthAfter i := by
      intro old
      obtain ⟨birth, birthHistory, birthAfter, birthReach, birthBound, birthRun, same⟩ := ih old
      have behind := previous.record_family_before old
      refine ⟨birth, birthHistory, birthAfter, birthReach, birthBound, birthRun, ?_⟩
      intro i hi
      rw [scan_step_prefix_rowAt run (by omega)]
      exact same i hi
    by_cases empty : ss = []
    · simp only [empty, List.isEmpty_nil, if_true] at member
      exact inherit member
    · simp only [List.isEmpty_iff, empty, if_false] at member
      rcases List.mem_cons.mp member with same | old
      · cases same
        exact ⟨before, history, after, previous, bound, run, fun _ _ => rfl⟩
      · exact inherit old

theorem recordAt_mem {rec : Records} {owner : Nat} {sources : List Nat}
    (lookup : recordAt rec owner = some sources) : (owner, sources) ∈ rec := by
  unfold recordAt at lookup
  obtain ⟨entry, found, same⟩ := Option.map_eq_some_iff.mp lookup
  have member := List.mem_of_find?_eq_some found
  have ownerEq : entry.1 = owner := by simpa using List.find?_some found
  rcases entry with ⟨i, ss⟩
  dsimp only at same ownerEq
  subst i; subst sources
  exact member

theorem ScanReach.lookup_before {initial current : Pattern} {start cursor owner : Nat}
    {rec : Records} {sources : List Nat} (reach : ScanReach initial start current rec cursor)
    (lookup : recordAt rec owner = some sources) : owner + sources.length < cursor :=
  reach.record_family_before (recordAt_mem lookup)

end IBLP
