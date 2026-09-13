import IBLP.Model.Products
import IBLP.Model.Powerset

namespace IBLP
open FullMarkedBLP
universe u

/-- The complete set of internal function graphs from one given set to
another. External functions absent from M are not added. -/
noncomputable def ModelStage.functionBook (stage : ModelStage.{u}) (domain range : stage.model.Element) :
    stage.model.Element :=
  stage.separation (rankPredicateAtom rankFunctionFormula ![2, 0, 1]) ![domain, range]
    (stage.powerset (stage.product domain range))

theorem ModelStage.mem_functionBook (stage : ModelStage.{u}) (domain range graph : stage.model.Element) :
    graph.val ∈ (stage.functionBook domain range).val ↔ ZFSet.IsFunc domain.val range.val graph.val := by
  rw [ModelStage.functionBook, stage.mem_separation, stage.model.realize_atom]
  have args : Fin.snoc ![domain, range] graph ∘ ![2, 0, 1] = ![graph, domain, range] := by
    funext i; fin_cases i <;> rfl
  rw [args, stage.model.functionFormula_realize, stage.model.function_absolute,
    stage.mem_powerset, stage.product_val]
  exact ⟨And.right, fun h => ⟨h.1, h⟩⟩

end IBLP
