import IBLP.Model.WeakAgreementAbsolute
import IBLP.Model.GraphBoundsAbsolute
import IBLP.Realization.MarkFormula
import IBLP.Realization.TraceGraphAbsolute
import IBLP.Realization.RetainedRowGraph
import IBLP.TraceBounds

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {M N : ModelStage.{u}} {a b : IBLP.Pattern}
  (D : FiniteBoundedData M a) (E : FiniteBoundedData N b)

theorem source_le_top (r : FiniteRowIndex a) : D.source r.val ≤ D.top := by
  rw [← D.point_top]
  exact (D.source_le_owner r).trans (D.point_increasing.monotoneOn
    (by change r.val ≤ a.length + 1; have := r.property.2; omega) (by change a.length + 1 ≤ a.length + 1; omega)
    (by have := r.property.2; omega))

theorem traceInput_le_top {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) :
    h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions ≤ D.top := by
  let bottom : FiniteRowIndex a := ⟨rows.getLast h.nonempty, h.validRows _ (List.getLast_mem h.nonempty)⟩
  change D.toFiniteTraceRows.toInternalTraceRows.source bottom.val ≤ D.top
  rw [D.toFiniteTraceRows.source_valid bottom]
  exact D.source_le_top bottom

theorem traceBound_le_top {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) :
    (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound ≤ D.top := by
  have startBound := (h.validRows start h.start_mem).2
  rw [← D.point_top]
  exact (h.bound_interval D.toFiniteTraceRows.toInternalTraceRows.actions).2.trans
    (D.point_increasing.monotoneOn (by change start + 1 ≤ a.length + 1; omega)
      (by change a.length + 1 ≤ a.length + 1; omega) (by omega))

/-- The saved graphs and the shared rank segment suffice for absolute mark
semantics. No equality of the ambient successor of the top is required. -/
theorem markCertificate_absolute (r : FiniteRowIndex a) (s : FiniteRowIndex b)
    {target start target' start' : Nat} {rows rows' : List Nat}
    (h : FactorTrace a target start rows) (h' : FactorTrace b target' start' rows')
    (carrier : (D.graph r).val = (E.graph s).val) (history : (D.traceGraph h).val = (E.traceGraph h').val)
    (shared : ∀ rho ≤ D.top, (M.hierarchy rho).val = (N.hierarchy rho).val) :
    h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val ↔
      h'.MarkCertificate E.toFiniteTraceRows.toInternalTraceRows s.val := by
  have rowBounds := (D.elementary r).bounds_absolute (E.elementary s) carrier
  have historyBounds := (D.traceGraph_elementary h).bounds_absolute (E.traceGraph_elementary h') history
  rw [← D.markFormula_realize r h, ← E.markFormula_realize s h']
  change modelWeakAgreementFormula.Realize ![D.graph r, D.traceGraph h, M.hierarchy (D.source r.val),
      M.hierarchy (h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions),
      M.hierarchy (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound] ↔
    modelWeakAgreementFormula.Realize ![E.graph s, E.traceGraph h', N.hierarchy (E.source s.val),
      N.hierarchy (h'.inputBound E.toFiniteTraceRows.toInternalTraceRows.actions),
      N.hierarchy (h'.word E.toFiniteTraceRows.toInternalTraceRows.actions).bound]
  rw [modelWeakAgreementFormula_realize, modelWeakAgreementFormula_realize]
  apply M.model.graphWeakAgreement_absolute N.model _ _ _ _ _ _ _ _ _ _ carrier history
  · exact (shared _ (D.source_le_top r)).trans
      (congrArg (fun rho => (N.hierarchy rho).val) rowBounds.1)
  · exact (shared _ (D.traceInput_le_top h)).trans
      (congrArg (fun rho => (N.hierarchy rho).val) historyBounds.1)
  · exact (shared _ (D.traceBound_le_top h)).trans
      (congrArg (fun rho => (N.hierarchy rho).val) historyBounds.2)

end IBLP.FiniteBoundedData
