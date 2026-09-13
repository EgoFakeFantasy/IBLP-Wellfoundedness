import IBLP.Model.GraphBoundsAbsolute
import IBLP.Model.InternalWeakAction

namespace IBLP.ModelStage
open FullMarkedBLP
universe u

theorem representedWeakAction_absolute {M N : ModelStage.{u}} {alpha beta gamma delta : Ordinal.{u}}
    {graph : M.model.Element} {graph' : N.model.Element}
    {k : M.BoundedMap alpha beta} {l : N.BoundedMap gamma delta}
    (left : M.RepresentsBoundedMap graph k) (right : N.RepresentsBoundedMap graph' l)
    (same : graph.val = graph'.val) (z : M.model.Element) (z' : N.model.Element) (input : z.val = z'.val) :
    (M.weakAction k z).val = (N.weakAction l z').val := by
  have bounds := left.toInternalGraphElementary.bounds_absolute right.toInternalGraphElementary same
  rcases bounds with ⟨rfl, rfl⟩
  have cut : (M.rankCut alpha z).val = (N.rankCut alpha z').val := by
    rw [M.rankCut_val, N.rankCut_val, input]
  have edge := right.2 (N.rankCut alpha z')
  rw [← same, ← cut] at edge
  exact (left.1.2 (M.rankCut alpha z).val ((M.mem_hierarchy _ _).mpr (M.rankCut alpha z).property)).unique
    (left.2 (M.rankCut alpha z)) edge

/-- On the same set input, identical full graphs have identical weak values
in different models. The canonical input cut is absolute by its definition. -/
theorem weakAction_absolute {M N : ModelStage.{u}} {alpha beta gamma delta : Ordinal.{u}}
    {graph : M.model.Element} {graph' : N.model.Element}
    (left : M.InternalGraphElementary alpha beta graph)
    (right : N.InternalGraphElementary gamma delta graph') (same : graph.val = graph'.val)
    (z : M.model.Element) (z' : N.model.Element) (input : z.val = z'.val) :
    (M.weakAction left.toRankEmbedding z).val = (N.weakAction right.toRankEmbedding z').val :=
  representedWeakAction_absolute (RepresentsBoundedMap.of_internalGraphElementary left)
    (RepresentsBoundedMap.of_internalGraphElementary right) same z z' input

end IBLP.ModelStage
