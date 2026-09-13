import IBLP.Model.CountableImage

namespace IBLP
open FullMarkedBLP
universe u
variable (stage : ModelStage.{u}) {N : TransitiveClass.{u}} (j : stage.model.ElementaryMap N)

/-- These fixed-point facts require no closure hypothesis on the target. -/
theorem ModelStage.ordinal_zero_image_val : (j (stage.ordinal 0)).val = (0 : Ordinal.{u}).toZFSet := by
  have h := j.map_formula rankEmptyFormula ![stage.ordinal 0]
  have args : j ∘ ![stage.ordinal 0] = ![j (stage.ordinal 0)] := by funext i; fin_cases i; rfl
  rw [args, N.emptyFormula_realize, stage.model.emptyFormula_realize] at h
  simpa only [Ordinal.toZFSet_zero] using h.mpr (by simp [ModelStage.ordinal])

theorem ModelStage.ordinal_nat_image_val (n : Nat) :
    (j (stage.ordinal (n : Ordinal.{u}))).val = (n : Ordinal.{u}).toZFSet := by
  have h (k : Nat) : stage.ordinalImage j (k : Ordinal.{u}) = k := by
    induction k with
    | zero => simpa only [ModelStage.ordinalImage, Ordinal.rank_toZFSet] using
        congrArg ZFSet.rank (stage.ordinal_zero_image_val j)
    | succ k ih => rw [Nat.cast_succ, ← Order.succ_eq_add_one, stage.ordinalImage_succ,
        ih, Order.succ_eq_add_one]
  rw [stage.ordinalImage_compat, h]

theorem ModelStage.ordinal_omega_image_val :
    (j (stage.ordinal Ordinal.omega0)).val = Ordinal.omega0.toZFSet := by
  have h := j.map_formula rankFirstLimitFormula ![stage.ordinal Ordinal.omega0]
  have args : j ∘ ![stage.ordinal Ordinal.omega0] = ![j (stage.ordinal Ordinal.omega0)] := by
    funext i; fin_cases i; rfl
  rw [args, N.firstLimitFormula_absolute, stage.model.firstLimitFormula_absolute] at h
  exact (setFirstLimit_ordinal_iff ((j.isOrdinal_iff _).mpr (ZFSet.isOrdinal_toZFSet _))).mp
    (h.mpr setFirstLimit_omega)

end IBLP
