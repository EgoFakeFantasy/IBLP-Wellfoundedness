import IBLP.Model.GraphBoundsUnique
import IBLP.Realization.TraceGraphImage
import IBLP.Realization.MarkFormula

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a b : IBLP.Pattern}
  (D : FiniteBoundedData stage a) (E : FiniteBoundedData stage b)

/-- The actual carrier and history graphs determine all five parameters
of the finite weak-agreement formula, even when row labels have changed. -/
theorem markFormulaParameters_congr (r : FiniteRowIndex a) (s : FiniteRowIndex b)
    {target start target' start' : Nat} {rows rows' : List Nat}
    (h : FactorTrace a target start rows) (h' : FactorTrace b target' start' rows')
    (carrier : D.graph r = E.graph s) (history : D.traceGraph h = E.traceGraph h') :
    D.markFormulaParameters r h = E.markFormulaParameters s h' := by
  have rightCarrier := E.elementary s
  rw [← carrier] at rightCarrier
  have rowBounds := (D.elementary r).bounds_unique rightCarrier
  have sourceEq : D.source r.val = E.source s.val := rowBounds.1
  have rightHistory := E.traceGraph_elementary h'
  rw [← history] at rightHistory
  have historyBounds := (D.traceGraph_elementary h).bounds_unique rightHistory
  change ![D.graph r, D.traceGraph h, stage.hierarchy (D.source r.val),
      stage.hierarchy (h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions),
      stage.hierarchy (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound] =
    ![E.graph s, E.traceGraph h', stage.hierarchy (E.source s.val),
      stage.hierarchy (h'.inputBound E.toFiniteTraceRows.toInternalTraceRows.actions),
      stage.hierarchy (h'.word E.toFiniteTraceRows.toInternalTraceRows.actions).bound]
  rw [carrier, history, sourceEq, historyBounds.1, historyBounds.2]

theorem markCertificate_congr_graphs (r : FiniteRowIndex a) (s : FiniteRowIndex b)
    {target start target' start' : Nat} {rows rows' : List Nat}
    (h : FactorTrace a target start rows) (h' : FactorTrace b target' start' rows')
    (carrier : D.graph r = E.graph s) (history : D.traceGraph h = E.traceGraph h') :
    h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val ↔
      h'.MarkCertificate E.toFiniteTraceRows.toInternalTraceRows s.val := by
  rw [← D.markFormula_realize r h, ← E.markFormula_realize s h',
    D.markFormulaParameters_congr E r s h h' carrier history]

end IBLP.FiniteBoundedData
