import IBLP.Model.UniformAtoms
import IBLP.Model.CompositionImage
import IBLP.Model.WeakAgreementFormula

namespace IBLP.UniformDefinable
open FullMarkedBLP FirstOrder Language
universe u

theorem graph_edge : UniformDefinable (fun (_ : ModelStage.{u}) (v : Fin 3 → _) =>
    ZFSet.pair (v 1).val (v 2).val ∈ (v 0).val) :=
  graph_applies.congr (fun stage v => stage.model.graphApplies_absolute _ _ _)

theorem graph_composition : UniformDefinable (fun (_ : ModelStage.{u}) (v : Fin 3 → _) =>
    graphCompositionSpec (v 0).val (v 1).val (v 2).val) :=
  (of_matrix graphCompositionFormula).congr (fun stage v => by
    have tuple : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
    rw [tuple, graphCompositionFormula_realize]
    rfl)

theorem function : UniformDefinable (fun (stage : ModelStage.{u}) (v : Fin 3 → _) =>
    stage.model.IsFunction (v 0) (v 1) (v 2)) :=
  (of_formula rankFunctionFormula).congr (fun stage v => by
    have tuple : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
    rw [tuple, stage.model.functionFormula_realize]
    rfl)

/-- Requiring an actual function graph excludes non-pair junk from the
edgewise specification of a composite. -/
theorem some_function : UniformDefinable (fun (stage : ModelStage.{u}) (v : Fin 1 → _) =>
    ∃ domain range, stage.model.IsFunction (v 0) domain range) :=
  function.exists_last.exists_last.congr (fun _ _ => Iff.rfl)

end IBLP.UniformDefinable
