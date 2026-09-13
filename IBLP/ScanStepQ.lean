import IBLP.FrozenQ
import IBLP.NativeQ
import IBLP.ScanGeometryHistory

namespace IBLP

/-- The expanded old base inherits exactly the frozen q value. Thus a q
increase in a complete actual scan step has an actual old-q completion
origin, and cannot be attributed to native lowering. -/
theorem scan_step_q_origin {initial result : Pattern} {rec : Records} {owner oldQ : Nat}
    {row : Row} {sources : List Nat} (valid : BasicValid initial) (shapes : OrdinaryShape initial)
    (proper : ProperMarks initial) (atRow : rowAt initial owner = some row) (hq : row.q = some oldQ)
    (history : FrozenGeometryBefore initial rec owner 0)
    (run : native (completeFrozenMarks initial rec owner) owner = some (result, sources)) :
    ∃ q, penultimate result owner = some q ∧
      (q = oldQ ∨ FrozenRaisedQ initial rec owner oldQ 0 q) := by
  have marked := completeFrozenMarks_invariant valid shapes proper history
  obtain ⟨out, q, atOut, outQ, origin⟩ :=
    (FrozenReach.finish initial rec owner).q_origin valid shapes proper atRow hq history
  exact ⟨q, native_base_q marked.valid marked.shapes run atOut outQ, origin⟩

/-- A strict increase across a scan step recovers the nonempty record
read at the original q mark and its exact width. -/
theorem scan_step_q_growth {initial result : Pattern} {rec : Records} {owner oldQ q : Nat}
    {row : Row} {sources : List Nat} (valid : BasicValid initial) (shapes : OrdinaryShape initial)
    (proper : ProperMarks initial) (atRow : rowAt initial owner = some row) (hq : row.q = some oldQ)
    (history : FrozenGeometryBefore initial rec owner 0)
    (run : native (completeFrozenMarks initial rec owner) owner = some (result, sources))
    (atResult : penultimate result owner = some q) (growth : oldQ < q) :
    FrozenRaisedQ initial rec owner oldQ 0 q := by
  obtain ⟨actual, actualAt, origin⟩ := scan_step_q_origin valid shapes proper atRow hq history run
  have same := Option.some.inj (actualAt.symm.trans atResult)
  subst actual
  exact origin.resolve_left (by omega)

end IBLP
