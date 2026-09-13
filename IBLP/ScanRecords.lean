import IBLP.ScanSaturation
import IBLP.ScanRecordBirth
import IBLP.NativeRecordedGeometry
import IBLP.TraceBounds

namespace IBLP

/-- Only strictly earlier native inputs are certified. The current
completion event is deliberately outside this history premise. -/
def ScanPriorSyntax (initial : Pattern) (start limit : Nat) : Prop :=
  ∀ before history owner, ScanReach initial start before history owner → owner < limit →
    BasicValid (completeFrozenMarks before history owner) ∧
      OrdinaryShape (completeFrozenMarks before history owner) ∧
      ProperMarks (completeFrozenMarks before history owner)

theorem ScanPriorSyntax.mono {initial : Pattern} {start lower upper : Nat}
    (history : ScanPriorSyntax initial start upper) (bound : lower ≤ upper) :
    ScanPriorSyntax initial start lower :=
  fun before rec owner reach less => history before rec owner reach (lt_of_lt_of_le less bound)

theorem ScanSyntaxHistory.prior {initial : Pattern} {start : Nat}
    (history : ScanSyntaxHistory initial start) (limit : Nat) : ScanPriorSyntax initial start limit :=
  fun before rec owner reach _ => history before rec owner reach

theorem ScanReach.record_source_bounds {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) (history : ScanPriorSyntax initial start cursor)
    {owner : Nat} {sources : List Nat} (member : (owner, sources) ∈ rec) :
    sources.Pairwise (· > ·) ∧ ∀ s ∈ sources, 0 < s ∧ s < owner := by
  obtain ⟨before, records, after, birth, _, run, _⟩ := reach.record_birth member
  have behind := reach.record_family_before member
  have invariants := history before records owner birth (by omega)
  exact native_record_source_bounds invariants.1 invariants.2.1 run

theorem ScanReach.record_predecessor {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) (history : ScanPriorSyntax initial start cursor)
    {owner s : Nat} {sources : List Nat} (member : (owner, sources) ∈ rec) (source : s ∈ sources) :
    predecessor current (owner + ((sources.filter (· < s)).length + 1)) = some s := by
  obtain ⟨before, records, after, birth, _, run, same⟩ := reach.record_birth member
  have behind := reach.record_family_before member
  have invariants := history before records owner birth (by omega)
  have rankBound : (sources.filter (· < s)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨s, source, by simp⟩
  simpa only [predecessor, same _ (by omega : owner + ((sources.filter (· < s)).length + 1) ≤ owner + sources.length)] using
    native_source_predecessor invariants.1 invariants.2.1 run source

theorem ScanReach.record_target_q {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) (history : ScanPriorSyntax initial start cursor)
    {owner j : Nat} {sources : List Nat} (member : (owner, sources) ∈ rec)
    (positive : 0 < j) (bound : j ≤ sources.length) : penultimate current (owner + j) = some (owner + j - 1) := by
  obtain ⟨before, records, after, birth, _, run, same⟩ := reach.record_birth member
  have behind := reach.record_family_before member
  have invariants := history before records owner birth (by omega)
  simpa only [penultimate, same _ (by omega : owner + j ≤ owner + sources.length)] using
    native_target_q invariants.1 invariants.2.1 run positive bound

/-- The actual ascending source order determines the corresponding
family predecessor, including every position of an arbitrarily long record. -/
theorem ScanReach.record_ascending_predecessor {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) (history : ScanPriorSyntax initial start cursor)
    {owner j s : Nat} {sources : List Nat} (member : (owner, sources) ∈ rec)
    (entry : sources.reverse[j]? = some s) : predecessor current (owner + j + 1) = some s := by
  have decreasing := (reach.record_source_bounds history member).1
  have rank := FullMarkedBLP.sorted_rank_at_index decreasing.reverse entry
  simp only [List.filter_reverse, List.length_reverse] at rank
  have source := List.mem_reverse.mp (List.mem_of_getElem? entry)
  have pred := reach.record_predecessor history member source
  simpa only [rank, Nat.add_assoc] using pred

theorem ScanReach.record_factorTrace {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) (history : ScanPriorSyntax initial start cursor)
    {owner j s : Nat} {sources : List Nat} (member : (owner, sources) ∈ rec)
    (entry : sources.reverse[j]? = some s) :
    FactorTrace current s (owner + j + 1) [owner + j + 1] := by
  have source := List.mem_reverse.mp (List.mem_of_getElem? entry)
  have below := (reach.record_source_bounds history member).2 s source
  exact .single (reach.record_ascending_predecessor history member entry) (by omega)

end IBLP
