import IBLP.Model.SetSatisfactionCorrectness
import IBLP.Model.SetSyntaxBooksImage

namespace IBLP
open FullMarkedBLP
universe u

/-- The single finite satisfaction formula, with its six fixed syntax sets,
transports the entire satisfaction set. No assumption that j fixes D is used. -/
theorem ModelStage.setSatisfaction_image (source target : ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (D : source.model.Element) :
    j (source.setSatisfaction D) = target.setSatisfaction (j D) := by
  have transfer := j.map_formula setSatisfactionFormula
    (Fin.snoc (Fin.snoc source.syntaxBooks D) (source.setSatisfaction D))
  have args : j ∘ Fin.snoc (Fin.snoc source.syntaxBooks D) (source.setSatisfaction D) =
      Fin.snoc (Fin.snoc target.syntaxBooks (j D)) (j (source.setSatisfaction D)) := by
    funext i
    cases i using Fin.lastCases with
    | last => simp [Fin.snoc]
    | cast i =>
      cases i using Fin.lastCases with
      | last => simp [Fin.snoc]
      | cast i => simpa using source.syntaxBooks_image target j i
  rw [args] at transfer
  exact Subtype.ext ((target.setSatisfaction_formula_iff (j D) _).mp
    (transfer.mpr (source.setSatisfaction_formula D)))

end IBLP
