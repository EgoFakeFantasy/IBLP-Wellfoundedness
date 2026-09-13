import IBLP.FrozenReach

namespace IBLP

/-- Only actual successful completions strictly before the indicated
pending-list length need geometry. At a nonempty queue the current event
is excluded. This is an obligation of the eventual joint event induction. -/
def FrozenGeometryBefore (initial : Pattern) (rec : Records) (owner remaining : Nat) : Prop :=
  ∀ current mark pending, FrozenReach initial rec owner current (mark :: pending) →
    remaining < (mark :: pending).length →
    ∀ row sources, rowAt current owner = some row →
      completionRecord current rec owner mark = some sources →
      Nonempty (row.CompletionGeometry owner mark sources)

theorem FrozenGeometryBefore.mono {initial : Pattern} {rec : Records} {owner lower upper : Nat}
    (history : FrozenGeometryBefore initial rec owner lower) (bound : lower ≤ upper) :
    FrozenGeometryBefore initial rec owner upper :=
  fun current mark pending reach earlier => history current mark pending reach (by omega)

theorem Row.CompletionGeometry.set_endpoint {a : Pattern} {owner mark : Nat} {row : Row}
    {sources : List Nat} (atRow : rowAt a owner = some row) (valid : row.BasicValid owner)
    (shape : row.OrdinaryShape) (C : row.CompletionGeometry owner mark sources) (i : Nat) :
    (rowAt (a.set (owner - 1) (completeMarkRow row mark sources)) i).bind Row.e =
      (rowAt a i).bind Row.e := by
  by_cases same : i = owner
  · subst i
    obtain ⟨e, he⟩ := fromRight_exists (xs := row.columns) (Row.step_pos shape) (Row.step_lt_length shape).le
    simp only [rowAt_set_self atRow, atRow, Option.bind_some]
    exact (C.preserves_e valid shape he).trans he.symm
  · rw [rowAt_set_other atRow same]

/-- The accumulated conclusion retains both local syntax and the original
p/e data. A geometry premise is never consumed for the current event. -/
structure FrozenInvariant (initial current : Pattern) : Prop where
  valid : BasicValid current
  shapes : OrdinaryShape current
  proper : ProperMarks current
  predecessors : ∀ i, predecessor current i = predecessor initial i
  endpoints : ∀ i, (rowAt current i).bind Row.e = (rowAt initial i).bind Row.e

theorem FrozenReach.invariant {initial current : Pattern} {rec : Records} {owner : Nat}
    {pending : List Nat} (reach : FrozenReach initial rec owner current pending)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : FrozenGeometryBefore initial rec owner pending.length) :
    FrozenInvariant initial current := by
  induction reach with
  | start => exact ⟨valid, shapes, proper, fun _ => rfl, fun _ => rfl⟩
  | @next before mark pending previous ih =>
    have earlier : pending.length < (mark :: pending).length := by simp
    have old := ih (history.mono earlier.le)
    unfold completeMark
    split
    · rename_i row sources atRow guard
      obtain ⟨C⟩ := history before mark pending previous earlier row sources atRow guard
      have out := C.set_syntax old.valid old.shapes old.proper atRow
      refine ⟨out.1, out.2.1, out.2.2, ?_, ?_⟩
      · intro i
        exact (C.set_predecessor atRow (old.valid _ _ atRow)
          (old.shapes row (rowAt_mem atRow)) i).trans (old.predecessors i)
      · intro i
        exact (C.set_endpoint atRow (old.valid _ _ atRow)
          (old.shapes row (rowAt_mem atRow)) i).trans (old.endpoints i)
    · exact old

theorem completeFrozenMarks_invariant {initial : Pattern} {rec : Records} {owner : Nat}
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : FrozenGeometryBefore initial rec owner 0) :
    FrozenInvariant initial (completeFrozenMarks initial rec owner) :=
  (FrozenReach.finish initial rec owner).invariant valid shapes proper history

theorem FrozenReach.factorTrace {initial current : Pattern} {rec : Records} {owner : Nat}
    {pending : List Nat} (reach : FrozenReach initial rec owner current pending)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : FrozenGeometryBefore initial rec owner pending.length)
    {target start : Nat} {rows : List Nat} (trace : FactorTrace initial target start rows) :
    FactorTrace current target start rows :=
  trace.of_predecessor_eq (reach.invariant valid shapes proper history).predecessors

end IBLP
