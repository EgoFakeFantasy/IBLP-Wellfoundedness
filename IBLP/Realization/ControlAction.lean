import IBLP.Model.BoundedActionCongruence
import IBLP.Extender.ControlRho
import IBLP.Realization.CopyActions

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem lastAction_eq (nonempty : 0 < a.length) :
    D.toFiniteTraceRows.toInternalTraceRows.actions.action a.length =
      stage.boundedCutAction (D.point_limit (rowEndpoint a a.length)) (D.lastDerivation nonempty).map := by
  change D.toFiniteTraceRows.toInternalTraceRows.actions.action (lastIndex nonempty).val = _
  rw [D.toFiniteTraceRows.action_valid (lastIndex nonempty)]
  exact stage.boundedCutAction_congr_graphs _ _ (D.graph_represents (lastIndex nonempty))
    (D.lastDerivation nonempty).represents rfl

/-- The actual control mark gives the first inequality in (5.7), for any
ordinal input, directly from its clipped ordinal-action equality. -/
theorem control_trace_rho_le_image (nonempty : 0 < a.length)
    {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows)
    (certificate : h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows a.length) (eta : Ordinal.{u}) :
    (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).rho eta ≤
      stage.ordinalImage (D.lastExtension nonempty).embedding eta := by
  have allInputs := (h.markCertificate_iff_allInputs D.toFiniteTraceRows.toInternalTraceRows a.length).mp certificate
  rw [D.lastAction_eq nonempty] at allInputs
  have bound := stage.allInputAgreement_rho_le allInputs
    (fun eta => stage.weakAction_ordinal (D.lastDerivation nonempty).map eta)
    (fun eta => h.ordinal_action D.toFiniteTraceRows.toInternalTraceRows.actions eta) eta
  exact bound.trans ((D.lastExtension nonempty).control_rho_le_image eta)

end IBLP.FiniteBoundedData
