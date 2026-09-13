import IBLP.Extender.GlobalExtensionality

namespace IBLP.Extender.Derivation
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}

noncomputable def naturalTest (ha : Order.IsSuccLimit alpha) (n : Nat) : Test stage alpha :=
  stage.rankOrdinal ⟨n, ((Ordinal.natCast_lt_omega0 n).trans_le (Ordinal.omega0_le_of_isSuccLimit ha)).trans
    (Order.lt_succ alpha)⟩

@[simp] theorem naturalTest_val (ha : Order.IsSuccLimit alpha) (n : Nat) :
    (naturalTest (stage := stage) ha n).val = (n : Ordinal.{u}).toZFSet := rfl

theorem map_naturalTest (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta) (n : Nat) :
    D.map (naturalTest ha n) = naturalTest hb n := by
  induction n with
  | zero =>
    have h := D.map.map_formula rankEmptyFormula ![naturalTest ha 0]
    have args : D.map ∘ ![naturalTest ha 0] = ![D.map (naturalTest ha 0)] := by
      funext i; fin_cases i; rfl
    rw [args, (stage.model.rankPart (Order.succ alpha)).emptyFormula_realize,
      (stage.model.rankPart (Order.succ beta)).emptyFormula_realize] at h
    exact Subtype.ext (by simpa using h.mpr (by simp))
  | succ n ih =>
    have h := D.map.map_formula modelSuccessorFormula ![naturalTest ha (n + 1), naturalTest ha n]
    have args : D.map ∘ ![naturalTest ha (n + 1), naturalTest ha n] =
        ![D.map (naturalTest ha (n + 1)), D.map (naturalTest ha n)] := by
      funext i; fin_cases i <;> rfl
    rw [args, (stage.model.rankPart (Order.succ alpha)).successorFormula_realize,
      (stage.model.rankPart (Order.succ beta)).successorFormula_realize] at h
    have source : (naturalTest (stage := stage) ha (n + 1)).val =
        insert (naturalTest (stage := stage) ha n).val (naturalTest (stage := stage) ha n).val := by
      simpa only [naturalTest_val, Nat.cast_add, Nat.cast_one] using Ordinal.toZFSet_add_one (n : Ordinal.{u})
    apply Subtype.ext
    rw [h.mpr source, ih, naturalTest_val, naturalTest_val]
    simpa only [Nat.cast_add, Nat.cast_one] using (Ordinal.toZFSet_add_one (n : Ordinal.{u})).symm

noncomputable def omegaTest (ha : Order.IsSuccLimit alpha) : Test stage alpha :=
  stage.rankOrdinal ⟨Ordinal.omega0, Order.lt_succ_of_le (Ordinal.omega0_le_of_isSuccLimit ha)⟩

@[simp] theorem omegaTest_val (ha : Order.IsSuccLimit alpha) :
    (omegaTest (stage := stage) ha).val = Ordinal.omega0.toZFSet := rfl

theorem map_omegaTest (D : Derivation stage alpha beta)
    (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta) : D.map (omegaTest ha) = omegaTest hb := by
  have h := D.map.map_formula rankFirstLimitFormula ![omegaTest ha]
  have args : D.map ∘ ![omegaTest ha] = ![D.map (omegaTest ha)] := by
    funext i; fin_cases i; rfl
  rw [args, (stage.model.rankPart (Order.succ alpha)).firstLimitFormula_absolute,
    (stage.model.rankPart (Order.succ beta)).firstLimitFormula_absolute] at h
  apply Subtype.ext
  exact (setFirstLimit_ordinal_iff ((D.map.isOrdinal_iff _).mpr (ZFSet.isOrdinal_toZFSet _))).mp
    (h.mpr setFirstLimit_omega)

end IBLP.Extender.Derivation
