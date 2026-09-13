import IBLP.Goal
import IBLP.Realization.RealizationBelowFormula

namespace IBLP
universe u

/-- Every complete realization is accessible for the original child
relation. The finite formula reflection premise is fully discharged. -/
theorem BoundedRealization.acc {stage : ModelStage.{u}} {a : Pattern}
    (R : BoundedRealization stage a) : Acc Child a :=
  R.acc_of_below_reflection
    (reflects_realizationBelow_of_definable UniformDefinable.realization_below stage)

/-- Manuscript theorem 1.1: the original six-row root, original full-tail
copying, frozen scan, native lowering and expansion relation are well founded
under precisely I3. -/
theorem i3_wellFoundedAtRoot (large : I3.{u}) : WellFoundedAtRoot :=
  i3_acc_of_definable_realizationBelow UniformDefinable.realization_below large

theorem i3_wellFoundedStatement : I3WellFoundedStatement.{u} := i3_wellFoundedAtRoot

theorem Reachable.acc {a : Pattern} (reachable : Reachable a) (large : I3.{u}) : Acc Child a := by
  induction reachable with
  | root => exact i3_wellFoundedAtRoot large
  | step _ child ih => exact ih.inv child

/-- In particular the literal original expansion tree has no infinite
branch starting at its original six-row root. -/
theorem i3_no_infinite_branch (large : I3.{u}) :
    ¬ ∃ branch : Nat → Pattern, branch 0 = root ∧ ∀ n, Child (branch (n + 1)) (branch n) := by
  intro branch
  exact (not_acc_iff_exists_descending_chain.mpr branch) (i3_wellFoundedAtRoot large)

end IBLP
