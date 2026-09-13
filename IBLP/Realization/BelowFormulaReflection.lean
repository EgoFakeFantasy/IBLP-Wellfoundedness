import IBLP.Realization.MinimalBadTop
import IBLP.Model.UniformDefinability
import IBLP.Realization.RootRealization

namespace IBLP
universe u

def realizationBelowPredicate (a : Pattern) : StagePredicate.{u} 1 := fun stage values =>
  ZFSet.IsOrdinal (values 0).val ∧ RealizationBelow stage a (values 0).val.rank

/-- Once each fixed pattern's actual complete-realization predicate has a
finite formula, full elementary reflection supplies the remaining minimum
argument. Formula existence is an explicit obligation, never an axiom. -/
theorem reflects_realizationBelow_of_definable
    (defined : ∀ a, UniformDefinable (realizationBelowPredicate.{u} a))
    (source : ModelStage.{u}) : ReflectsRealizationBelow source := by
  intro target j a bound below
  have actual : realizationBelowPredicate a target (j ∘ ![source.ordinal bound]) := by
    refine ⟨(j.isOrdinal_iff _).mpr (ZFSet.isOrdinal_toZFSet bound), ?_⟩
    exact below
  have reflected := ((defined a).reflect_iff source target j ![source.ordinal bound]).mp actual
  simpa only [realizationBelowPredicate, Matrix.cons_val_zero, ModelStage.ordinal, Ordinal.rank_toZFSet] using reflected.2

theorem i3_acc_of_definable_realizationBelow
    (defined : ∀ a, UniformDefinable (realizationBelowPredicate.{u} a)) (large : I3.{u}) : Acc Child root := by
  obtain ⟨R⟩ := exists_bounded_root_of_i3 large
  exact R.acc_of_below_reflection (reflects_realizationBelow_of_definable defined initialStage)

end IBLP
