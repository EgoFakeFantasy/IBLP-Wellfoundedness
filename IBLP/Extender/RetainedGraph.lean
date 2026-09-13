import IBLP.Extender.Extension
import IBLP.Model.GraphElementaryAbsolute

namespace IBLP.Extender.InternalExtension
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {D : Derivation stage alpha beta}
  (E : InternalExtension D)

noncomputable def retain (x : stage.model.Element) (below : x.val.rank < beta) : E.next.model.Element :=
  ⟨x.val, (E.rank_mem_iff x.val below).mpr x.property⟩

theorem hierarchy_below (rho : Ordinal.{u}) (below : rho ≤ beta) :
    (E.next.hierarchy rho).val = (stage.hierarchy rho).val := by
  apply ZFSet.ext
  intro x
  rw [E.next.mem_hierarchy, stage.mem_hierarchy]
  constructor
  · exact fun h => ⟨E.inside h.1, h.2⟩
  · exact fun h => ⟨(E.rank_mem_iff x (h.2.trans_le below)).mpr h.1, h.2⟩

theorem graph_rank_lt (hb : Order.IsSuccLimit beta) (rho sigma : Ordinal.{u})
    (hr : rho < beta) (hs : sigma < beta) (graph : stage.model.Element)
    (elementary : stage.InternalGraphElementary rho sigma graph) : graph.val.rank < beta := by
  apply rank_function_lt_of_limit hb ?_ ?_ ((stage.model.function_absolute _ _ _).mp elementary.1)
  · rw [stage.hierarchy_rank]
    exact hb.succ_lt hr
  · rw [stage.hierarchy_rank]
    exact hb.succ_lt hs

/-- Old rows are retained as the very same complete set graphs. Their
elementarity uses equality of both entire successor-rank structures. -/
theorem retained_elementary (hb : Order.IsSuccLimit beta) (rho sigma : Ordinal.{u})
    (hr : rho < beta) (hs : sigma < beta) (graph : stage.model.Element)
    (elementary : stage.InternalGraphElementary rho sigma graph) :
    E.next.InternalGraphElementary rho sigma
      (E.retain graph (graph_rank_lt hb rho sigma hr hs graph elementary)) := by
  exact (stage.model.graphElementary_absolute E.next.model graph _ _ _ _ _ rfl
    (E.hierarchy_below (Order.succ rho) (hb.succ_lt hr).le).symm
    (E.hierarchy_below (Order.succ sigma) (hb.succ_lt hs).le).symm).mp elementary

end IBLP.Extender.InternalExtension
