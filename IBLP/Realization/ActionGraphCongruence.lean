import IBLP.Realization.TraceActionAbsolute
import IBLP.Rank.ActionCongruence

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a b : IBLP.Pattern}
  (D : FiniteBoundedData stage a) (E : FiniteBoundedData stage b)

theorem rowAction_congr_graphs (r : FiniteRowIndex a) (s : FiniteRowIndex b)
    (graph : D.graph r = E.graph s) :
    D.toFiniteTraceRows.toInternalTraceRows.actions.action r.val =
      E.toFiniteTraceRows.toInternalTraceRows.actions.action s.val := by
  rw [D.toFiniteTraceRows.action_valid, E.toFiniteTraceRows.action_valid]
  have same := congrArg Subtype.val graph
  have bounds := (D.elementary r).bounds_absolute (E.elementary s) same
  apply CutAction.ext
  · funext z
    apply Subtype.ext
    exact ModelStage.representedWeakAction_absolute (D.graph_represents r) (E.graph_represents s) same z z rfl
  · funext eta
    have values := ModelStage.representedWeakAction_absolute (D.graph_represents r) (E.graph_represents s)
      same (stage.ordinal eta) (stage.ordinal eta) rfl
    rw [stage.weakAction_ordinal, stage.weakAction_ordinal] at values
    exact Ordinal.toZFSet_injective values
  · exact bounds.2

theorem traceAction_congr_graphs {target start target' start' : Nat} {rows rows' : List Nat}
    (h : FactorTrace a target start rows) (h' : FactorTrace b target' start' rows')
    (graph : D.traceGraph h = E.traceGraph h') :
    h.word D.toFiniteTraceRows.toInternalTraceRows.actions = h'.word E.toFiniteTraceRows.toInternalTraceRows.actions := by
  have same := congrArg Subtype.val graph
  apply CutAction.ext
  · funext z
    exact Subtype.ext (D.traceAction_congr_values E h h' same z z rfl)
  · exact funext (D.traceRho_congr_values E h h' same)
  · exact ((D.traceGraph_elementary h).bounds_absolute (E.traceGraph_elementary h') same).2

end IBLP.FiniteBoundedData
