import IBLP.Model.WeakActionAbsolute
import IBLP.Realization.TraceGraphAbsolute

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {M N : ModelStage.{u}} {a b : IBLP.Pattern}
  (D : FiniteBoundedData M a) (E : FiniteBoundedData N b)

theorem traceAction_congr_values {target start target' start' : Nat} {rows rows' : List Nat}
    (h : FactorTrace a target start rows) (h' : FactorTrace b target' start' rows')
    (graph : (D.traceGraph h).val = (E.traceGraph h').val)
    (z : M.model.Element) (z' : N.model.Element) (input : z.val = z'.val) :
    ((h.word D.toFiniteTraceRows.toInternalTraceRows.actions).act z).val =
      ((h'.word E.toFiniteTraceRows.toInternalTraceRows.actions).act z').val := by
  rw [← h.internalComposite_weakAction D.toFiniteTraceRows.toInternalTraceRows,
    ← h'.internalComposite_weakAction E.toFiniteTraceRows.toInternalTraceRows]
  exact ModelStage.representedWeakAction_absolute
    (h.internalCompositeGraph_represents D.toFiniteTraceRows.toInternalTraceRows (D.graphs_on_trace h))
    (h'.internalCompositeGraph_represents E.toFiniteTraceRows.toInternalTraceRows (E.graphs_on_trace h'))
    graph z z' input

theorem traceRho_congr_values {target start target' start' : Nat} {rows rows' : List Nat}
    (h : FactorTrace a target start rows) (h' : FactorTrace b target' start' rows')
    (graph : (D.traceGraph h).val = (E.traceGraph h').val) (eta : Ordinal.{u}) :
    (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).rho eta =
      (h'.word E.toFiniteTraceRows.toInternalTraceRows.actions).rho eta := by
  have values := D.traceAction_congr_values E h h' graph (M.ordinal eta) (N.ordinal eta) rfl
  change ((h.word D.toFiniteTraceRows.toInternalTraceRows.actions).act (M.ordinalView.elem eta)).val =
    ((h'.word E.toFiniteTraceRows.toInternalTraceRows.actions).act (N.ordinalView.elem eta)).val at values
  rw [h.ordinal_action D.toFiniteTraceRows.toInternalTraceRows.actions,
    h'.ordinal_action E.toFiniteTraceRows.toInternalTraceRows.actions] at values
  exact Ordinal.toZFSet_injective values

end IBLP.FiniteBoundedData
