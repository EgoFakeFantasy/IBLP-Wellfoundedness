import IBLP.Realization.ExpandTotal
import IBLP.Realization.RootRealization

namespace IBLP
universe u

/-- Every finitely reachable original pattern has a complete bounded
realization in an actual model stage, starting from the original I3 root.
This is finite reachability, not yet exclusion of an infinite branch. -/
theorem Reachable.bounded_realization {a : Pattern} (reachable : Reachable a) (large : I3.{u}) :
    ∃ stage : ModelStage.{u}, Nonempty (BoundedRealization stage a) := by
  induction reachable with
  | root => exact ⟨initialStage, exists_bounded_root_of_i3 large⟩
  | @step parent child previous relation ih =>
    obtain ⟨stage, ⟨R⟩⟩ := ih
    obtain ⟨m, run⟩ := relation
    obtain ⟨next, _, S, _⟩ := R.expand_realization run
    exact ⟨next, ⟨S⟩⟩

/-- Every parameter of the manuscript program is defined at each
reachable nonzero pattern. All conclusions use the exact original Child
relation and the six-row root. -/
theorem Reachable.expand_total {a : Pattern} (reachable : Reachable a) (large : I3.{u})
    (nonempty : a ≠ zero) (m : Nat) : ∃ b, expand a m = some b := by
  obtain ⟨stage, ⟨R⟩⟩ := reachable.bounded_realization large
  have positive : 0 < a.length := by cases a <;> simp_all [zero]
  exact R.expand_total positive m

end IBLP
