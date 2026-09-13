import IBLP.Model.WeakAgreementFormula
import IBLP.Realization.MarkCertificate

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

namespace FactorTrace
variable {stage : ModelStage.{u}} {a : Pattern} {theta : Nat → Ordinal.{u}}
  (R : InternalTraceRows stage a theta) {target start : Nat} {rows : List Nat}

/-- The finite formula uses the actual carrier graph, actual historical
composite graph, their own source cuts and the computed natural bound. -/
theorem markCertificate_iff_graphWeakAgreement (h : FactorTrace a target start rows)
    (carrier : Nat) {carrierGraph : stage.model.Element}
    (represented : stage.RepresentsBoundedMap carrierGraph (R.map carrier))
    (graphs : ∀ r ∈ rows, ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph (R.map r)) :
    h.MarkCertificate R carrier ↔
      stage.model.GraphWeakAgreement carrierGraph (h.internalCompositeGraph R graphs)
        (stage.hierarchy (R.source carrier)) (stage.hierarchy (h.inputBound R.actions))
        (stage.hierarchy (h.word R.actions).bound) := by
  rw [stage.graphWeakAgreement_iff represented (h.internalCompositeGraph_represents R graphs)
    (R.source_limit carrier) (h.internal_inputBound_limit R)]
  unfold MarkCertificate CutAction.WeakAgreement
  simp only [ModelStage.boundedCutAction, h.internalComposite_weakAction R]
  rfl

theorem markCertificate_formula_realize (h : FactorTrace a target start rows)
    (carrier : Nat) {carrierGraph : stage.model.Element}
    (represented : stage.RepresentsBoundedMap carrierGraph (R.map carrier))
    (graphs : ∀ r ∈ rows, ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph (R.map r)) :
    modelWeakAgreementFormula.Realize
      ![carrierGraph, h.internalCompositeGraph R graphs,
        stage.hierarchy (R.source carrier), stage.hierarchy (h.inputBound R.actions),
        stage.hierarchy (h.word R.actions).bound] ↔ h.MarkCertificate R carrier := by
  rw [modelWeakAgreementFormula_realize]
  exact (h.markCertificate_iff_graphWeakAgreement R carrier represented graphs).symm

end FactorTrace
end IBLP
