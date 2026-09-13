import IBLP.ScanLabels
import IBLP.ScanRecords
import IBLP.CompletionTrace

namespace IBLP

/-- A separate, strictly prior completion obligation. Native already
preserves old p edges under its exact shift. This premise must ultimately
come from the geometry of each actual earlier frozen completion. -/
def ScanPriorPredecessors (initial : Pattern) (start limit : Nat) : Prop :=
  ∀ before history owner, ScanReach initial start before history owner → owner < limit →
    ∀ i, predecessor (completeFrozenMarks before history owner) i = predecessor before i

theorem ScanPriorPredecessors.mono {initial : Pattern} {start lower upper : Nat}
    (history : ScanPriorPredecessors initial start upper) (bound : lower ≤ upper) :
    ScanPriorPredecessors initial start lower :=
  fun before rec owner reach less => history before rec owner reach (lt_of_lt_of_le less bound)

/-- Exact p-edge transport for entrance vertices. Both induction
obligations concern only native events strictly before the current cursor. -/
theorem ScanLabeledReach.predecessor_image {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names)
    (priorSyntax : ScanPriorSyntax initial start (names oldCursor))
    (preserved : ScanPriorPredecessors initial start (names oldCursor))
    {i p : Nat} (pred : predecessor initial i = some p) :
    predecessor current (names i) = some (names p) := by
  induction reach with
  | start => exact pred
  | @next before result history old name sources previous bound run ih =>
    have earlier : name old < (shiftAfter (name old) sources.length ∘ name) (old + 1) := by
      rw [previous.next_cursor]
      omega
    have oldPred := ih (priorSyntax.mono earlier.le) (preserved.mono earlier.le)
    have invariants := priorSyntax before history (name old) previous.forget earlier
    have inputPred : predecessor (completeFrozenMarks before history (name old)) (name i) = some (name p) :=
      (preserved before history (name old) previous.forget earlier (name i)).trans oldPred
    exact native_predecessor_shift invariants.1 invariants.2.1 run inputPred

theorem ScanLabeledReach.factorTrace_image {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names)
    (priorSyntax : ScanPriorSyntax initial start (names oldCursor))
    (preserved : ScanPriorPredecessors initial start (names oldCursor))
    {target source : Nat} {rows : List Nat} (h : FactorTrace initial target source rows) :
    FactorTrace current (names target) (names source) (rows.map names) := by
  induction h with
  | single pred less => exact .single (reach.predecessor_image priorSyntax preserved pred) (reach.names_strictMono less)
  | cons pred less inner ih => exact .cons (reach.predecessor_image priorSyntax preserved pred) (reach.names_strictMono less) ih

theorem ScanLabeledReach.trace_image {initial current : Pattern} {start oldCursor : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names)
    (priorSyntax : ScanPriorSyntax initial start (names oldCursor))
    (preserved : ScanPriorPredecessors initial start (names oldCursor))
    {target source : Nat} {rows : List Nat} (h : Trace initial target source rows) :
    Trace current (names target) (names source) (rows.map names) := by
  induction h with
  | done => exact .done
  | step targetLess pred less inner ih =>
    exact .step (reach.names_strictMono targetLess) (reach.predecessor_image priorSyntax preserved pred)
      (reach.names_strictMono less) ih

/-- A copied block's entrance bounds are carried by the actual strict
old-label embedding, even when earlier native families have different sizes. -/
theorem ScanLabeledReach.factor_block_image {initial current : Pattern} {start oldCursor lower upper : Nat}
    {rec : Records} {names : Nat → Nat} (reach : ScanLabeledReach initial start current rec oldCursor names)
    {rows : List Nat} (bounds : ∀ i ∈ rows, lower ≤ i ∧ i < upper) :
    ∀ i ∈ rows.map names, names lower ≤ i ∧ i < names upper := by
  intro i member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  have bound := bounds old oldMember
  exact ⟨reach.names_strictMono.monotone bound.1, reach.names_strictMono bound.2⟩

end IBLP
