import IBLP.Model.SetSatisfactionFormulaGraph
import IBLP.Model.SetSatisfactionCorrectness

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

/-- Nine free set parameters: the six fixed syntax books, D, E and the graph.
Both truth sets are existentially constructed and certified by the single
finite satisfaction formula. No truth predicate or formula scheme occurs. -/
def setGraphElementaryMatrix : RankPredicateFormula 0 9 :=
  let source : RankPredicateFormula 0 11 :=
    setSatisfactionMatrix.relabelSets ![0, 1, 2, 3, 4, 5, 6, 9]
  let target : RankPredicateFormula 0 11 :=
    setSatisfactionMatrix.relabelSets ![0, 1, 2, 3, 4, 5, 7, 10]
  let preserves : RankPredicateFormula 0 11 :=
    setGraphPreservesSatisfaction.relabelSets ![8, 6, 7, 0, 9, 10]
  (source.and (target.and preserves)).ex.ex

def setGraphElementaryFormula : membershipLanguage.Formula (Fin 9) :=
  rankPredicateToFormula setGraphElementaryMatrix

theorem setGraphElementaryFormula_realize_withBooks (stage : ModelStage.{u})
    (books : Fin 6 → stage.model.Element) (D E graph : stage.model.Element) :
    setGraphElementaryFormula.Realize (Fin.snoc (Fin.snoc (Fin.snoc books D) E) graph) ↔
      ∃ sourceTruth targetTruth : stage.model.Element,
        SetCodedTruthConditions stage.model books D sourceTruth ∧
        SetCodedTruthConditions stage.model books E targetTruth ∧
        SetGraphPreservesSatisfaction stage.model graph D E (books 0) sourceTruth targetTruth := by
  rw [setGraphElementaryFormula, ← stage.model.realize_toFormula]
  simp only [setGraphElementaryMatrix, stage.model.realize_ex, stage.model.realize_and,
    stage.model.realize_relabel]
  have sourceTuple (s t : stage.model.Element) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc books D) E) graph) s) t ∘
        ![(0 : Fin 11), 1, 2, 3, 4, 5, 6, 9] = Fin.snoc (Fin.snoc books D) s := by
    funext i; fin_cases i <;> rfl
  have targetTuple (s t : stage.model.Element) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc books D) E) graph) s) t ∘
        ![(0 : Fin 11), 1, 2, 3, 4, 5, 7, 10] = Fin.snoc (Fin.snoc books E) t := by
    funext i; fin_cases i <;> rfl
  have mapTuple (s t : stage.model.Element) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc books D) E) graph) s) t ∘
        ![(8 : Fin 11), 6, 7, 0, 9, 10] = ![graph, D, E, books 0, s, t] := by
    funext i; fin_cases i <;> rfl
  simp only [sourceTuple, targetTuple, mapTuple, setSatisfactionMatrix_realize,
    setGraphPreservesSatisfaction_realize]

/-- Full graph elementarity between the two actual set membership structures
is expressed by this one fixed finite first-order formula. -/
theorem ModelStage.setGraphElementaryFormula_realize (stage : ModelStage.{u})
    (D E graph : stage.model.Element) :
    setGraphElementaryFormula.Realize
      (Fin.snoc (Fin.snoc (Fin.snoc stage.syntaxBooks D) E) graph) ↔
        stage.model.GraphElementary graph D E := by
  rw [setGraphElementaryFormula_realize_withBooks]
  constructor
  · rintro ⟨sourceTruth, targetTruth, sourceCorrect, targetCorrect, preserves⟩
    have sourceEq : sourceTruth = stage.setSatisfaction D := Subtype.ext sourceCorrect.truth_eq
    have targetEq : targetTruth = stage.setSatisfaction E := Subtype.ext targetCorrect.truth_eq
    rw [sourceEq, targetEq] at preserves
    exact (stage.graphElementary_iff_setSatisfaction graph D E).mpr preserves
  · intro elementary
    exact ⟨stage.setSatisfaction D, stage.setSatisfaction E,
      stage.setSatisfaction_coded D, stage.setSatisfaction_coded E,
      (stage.graphElementary_iff_setSatisfaction graph D E).mp elementary⟩

end IBLP
