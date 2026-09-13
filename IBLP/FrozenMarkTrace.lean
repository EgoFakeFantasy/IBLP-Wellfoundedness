import IBLP.FrozenGeometry
import IBLP.CompletionMarkTrace

namespace IBLP

/-- All already accurate old traces survive an actual frozen prefix.
The original terminal paired source is retained, not just the p chain. -/
theorem FrozenReach.markTrace {initial current : Pattern} {rec : Records} {owner : Nat}
    {pending : List Nat} (reach : FrozenReach initial rec owner current pending)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : FrozenGeometryBefore initial rec owner pending.length)
    {r mark : Nat} {rows : List Nat} (computed : markTrace initial r mark = some rows) :
    markTrace current r mark = some rows := by
  induction reach with
  | start => exact computed
  | @next before nextMark pending previous ih =>
    have earlier : pending.length < (nextMark :: pending).length := by simp
    have earlierHistory := history.mono earlier.le
    have old := previous.invariant valid shapes proper earlierHistory
    have retained := ih earlierHistory
    unfold completeMark
    split
    · rename_i row sources atRow guard
      obtain ⟨C⟩ := history before nextMark pending previous earlier row sources atRow guard
      exact C.set_markTrace old.valid old.shapes atRow retained
    · exact retained

theorem completeFrozenMarks_markTrace {initial : Pattern} {rec : Records} {owner : Nat}
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : FrozenGeometryBefore initial rec owner 0)
    {r mark : Nat} {rows : List Nat} (computed : markTrace initial r mark = some rows) :
    markTrace (completeFrozenMarks initial rec owner) r mark = some rows :=
  (FrozenReach.finish initial rec owner).markTrace valid shapes proper history computed

end IBLP
