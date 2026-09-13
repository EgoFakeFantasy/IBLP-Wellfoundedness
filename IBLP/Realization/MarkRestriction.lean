import IBLP.Realization.ActionGraphCongruence

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a b : IBLP.Pattern}
  (D : FiniteBoundedData stage a) (E : FiniteBoundedData stage b)

/-- Restrict both the saved carrier and the actual history word. The new
natural bound fits the new carrier by the literal trace/row positions. -/
theorem markCertificate_of_restrictions (i : FiniteRowIndex a) (j : FiniteRowIndex b)
    {target start target' start' : Nat} {rows rows' : List Nat}
    (h : FactorTrace a target start rows) (h' : FactorTrace b target' start' rows')
    (before : start' < j.val)
    (carrier : CutRestriction (E.toFiniteTraceRows.toInternalTraceRows.actions.action j.val)
      (D.toFiniteTraceRows.toInternalTraceRows.actions.action i.val))
    (history : CutRestriction (h'.word E.toFiniteTraceRows.toInternalTraceRows.actions)
      (h.word D.toFiniteTraceRows.toInternalTraceRows.actions))
    (certificate : h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows i.val) :
    h'.MarkCertificate E.toFiniteTraceRows.toInternalTraceRows j.val := by
  have bounds := h'.carrier_bound E.toFiniteTraceRows.toInternalTraceRows E.point_increasing j.property.2 before
  have fits : (h'.word E.toFiniteTraceRows.toInternalTraceRows.actions).bound ≤
      (E.toFiniteTraceRows.toInternalTraceRows.actions.action j.val).bound := by
    rw [E.toFiniteTraceRows.action_valid]
    exact bounds.2.1.trans bounds.2.2.le
  apply (h'.markCertificate_iff_allInputs E.toFiniteTraceRows.toInternalTraceRows j.val).mpr
  exact carrier.agreement history
    ((h.markCertificate_iff_allInputs D.toFiniteTraceRows.toInternalTraceRows i.val).mp certificate)
    history.bound_le fits le_rfl

end IBLP.FiniteBoundedData
