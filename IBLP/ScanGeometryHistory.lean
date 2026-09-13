import IBLP.FrozenGeometry
import IBLP.ScanLabelTrace

namespace IBLP

/-- Actual earlier rows and their actual frozen prefixes. This is the
geometric part of the joint event induction; no unexecuted or current
scan event is included. -/
def ScanPriorGeometry (initial : Pattern) (start limit : Nat) : Prop :=
  ∀ current rec cursor, ScanReach initial start current rec cursor → cursor < limit →
    FrozenGeometryBefore current rec cursor 0

theorem ScanPriorGeometry.mono {initial : Pattern} {start lower upper : Nat}
    (history : ScanPriorGeometry initial start upper) (bound : lower ≤ upper) :
    ScanPriorGeometry initial start lower :=
  fun current rec cursor reach earlier => history current rec cursor reach (by omega)

/-- Entrance syntax follows from the geometry of strictly earlier events
and the already proved exact native closure. -/
theorem ScanReach.syntax_of_geometry {initial current : Pattern} {start cursor : Nat} {rec : Records}
    (reach : ScanReach initial start current rec cursor) (valid : BasicValid initial)
    (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : ScanPriorGeometry initial start cursor) :
    BasicValid current ∧ OrdinaryShape current ∧ ProperMarks current := by
  induction reach with
  | start => exact ⟨valid, shapes, proper⟩
  | @next before after records owner sources previous bound run ih =>
    have earlier : owner < owner + sources.length + 1 := by omega
    have old := ih (history.mono earlier.le)
    have marked := completeFrozenMarks_invariant old.1 old.2.1 old.2.2
      (history before records owner previous earlier)
    exact native_preserves_syntax marked.valid marked.shapes marked.proper run

theorem ScanPriorGeometry.priorSyntax {initial : Pattern} {start limit : Nat}
    (history : ScanPriorGeometry initial start limit) (valid : BasicValid initial)
    (shapes : OrdinaryShape initial) (proper : ProperMarks initial) :
    ScanPriorSyntax initial start limit := by
  intro before records owner reach earlier
  have old := reach.syntax_of_geometry valid shapes proper (history.mono earlier.le)
  have out := completeFrozenMarks_invariant old.1 old.2.1 old.2.2
    (history before records owner reach earlier)
  exact ⟨out.valid, out.shapes, out.proper⟩

theorem ScanPriorGeometry.priorPredecessors {initial : Pattern} {start limit : Nat}
    (history : ScanPriorGeometry initial start limit) (valid : BasicValid initial)
    (shapes : OrdinaryShape initial) (proper : ProperMarks initial) :
    ScanPriorPredecessors initial start limit := by
  intro before records owner reach earlier
  have old := reach.syntax_of_geometry valid shapes proper (history.mono earlier.le)
  exact (completeFrozenMarks_invariant old.1 old.2.1 old.2.2
    (history before records owner reach earlier)).predecessors

theorem ScanLabeledReach.predecessor_image_of_geometry {initial current : Pattern}
    {start oldCursor : Nat} {rec : Records} {names : Nat → Nat}
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : ScanPriorGeometry initial start (names oldCursor))
    {i p : Nat} (pred : predecessor initial i = some p) :
    predecessor current (names i) = some (names p) :=
  reach.predecessor_image (history.priorSyntax valid shapes proper)
    (history.priorPredecessors valid shapes proper) pred

theorem ScanLabeledReach.factorTrace_image_of_geometry {initial current : Pattern}
    {start oldCursor : Nat} {rec : Records} {names : Nat → Nat}
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : ScanPriorGeometry initial start (names oldCursor))
    {target source : Nat} {rows : List Nat} (trace : FactorTrace initial target source rows) :
    FactorTrace current (names target) (names source) (rows.map names) :=
  reach.factorTrace_image (history.priorSyntax valid shapes proper)
    (history.priorPredecessors valid shapes proper) trace

/-- Before the current mark is executed, its prefix needs geometry only
from earlier scan rows and earlier marks of this same frozen queue. -/
theorem ScanReach.frozen_invariant_of_geometry {initial before current : Pattern}
    {start owner : Nat} {rec : Records} {pending : List Nat}
    (reach : ScanReach initial start before rec owner)
    (frozen : FrozenReach before rec owner current pending)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (earlierRows : ScanPriorGeometry initial start owner)
    (earlierMarks : FrozenGeometryBefore before rec owner pending.length) :
    FrozenInvariant before current := by
  have old := reach.syntax_of_geometry valid shapes proper earlierRows
  exact frozen.invariant old.1 old.2.1 old.2.2 earlierMarks

end IBLP
