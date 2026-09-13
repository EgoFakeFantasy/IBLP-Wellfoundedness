import IBLP.Model.UniformQuantifiers
import IBLP.Model.GraphCriticalPoint

namespace IBLP.UniformDefinable
open FullMarkedBLP FirstOrder Language
universe u

theorem of_formula {n : Nat} (phi : membershipLanguage.Formula (Fin n)) :
    UniformDefinable (fun (_ : ModelStage.{u}) values => phi.Realize values) :=
  (of_matrix (rankPredicateAtom phi id)).congr (fun stage values => by
    rw [stage.model.realize_atom, Function.comp_id])

theorem equal {n : Nat} (i j : Fin n) :
    UniformDefinable (fun (_ : ModelStage.{u}) values => values i = values j) :=
  of_matrix (.equal i j)

theorem member {n : Nat} (i j : Fin n) :
    UniformDefinable (fun (_ : ModelStage.{u}) values => (values i).val ∈ (values j).val) :=
  of_matrix (.member i j)

theorem ordinal : UniformDefinable (fun (_ : ModelStage.{u}) (values : Fin 1 → _) =>
    ZFSet.IsOrdinal (values 0).val) :=
  (of_formula rankOrdinalFormula).congr (fun stage values => by
    have tuple : values = ![values 0] := by funext i; fin_cases i; rfl
    rw [tuple, stage.model.ordinalFormula_realize]
    rfl)

theorem graph_applies : UniformDefinable (fun (stage : ModelStage.{u}) (values : Fin 3 → _) =>
    stage.model.GraphApplies (values 0) (values 1) (values 2)) :=
  (of_formula rankGraphAppliesFormula).congr (fun stage values => by
    have tuple : values = ![values 0, values 1, values 2] := by funext i; fin_cases i <;> rfl
    rw [tuple, stage.model.graphAppliesFormula_realize]
    rfl)

theorem graph_critical : UniformDefinable (fun (stage : ModelStage.{u}) (values : Fin 2 → _) =>
    stage.model.GraphCriticalPoint (values 0) (values 1)) :=
  (of_formula modelGraphCriticalPointFormula).congr (fun stage values => by
    have tuple : values = ![values 0, values 1] := by funext i; fin_cases i <;> rfl
    rw [tuple, modelGraphCriticalPointFormula_realize]
    rfl)

theorem inaccessible : UniformDefinable (fun (stage : ModelStage.{u}) (values : Fin 1 → _) =>
    stage.model.InternalInaccessible (values 0)) :=
  (of_matrix internalInaccessibleFormula).congr (fun stage values => by
    have tuple : values = ![values 0] := by funext i; fin_cases i; rfl
    rw [tuple, stage.model.internalInaccessibleFormula_realize]
    rfl)

/-- The graph atom covers full elementarity for all formulas, using the
already certified finite set-satisfaction formula and six syntax books. -/
theorem graph_elementary : UniformDefinable (fun (stage : ModelStage.{u}) (values : Fin 3 → _) =>
    stage.model.GraphElementary (values 2) (values 0) (values 1)) := by
  refine ⟨setGraphElementaryMatrix, ?_⟩
  intro stage values
  have tuple : Fin.append stage.syntaxBooks values =
      Fin.snoc (Fin.snoc (Fin.snoc stage.syntaxBooks (values 0)) (values 1)) (values 2) := by
    funext i
    fin_cases i <;> rfl
  rw [stage.model.realize_toFormula, tuple]
  exact stage.setGraphElementaryFormula_realize (values 0) (values 1) (values 2)

end IBLP.UniformDefinable
