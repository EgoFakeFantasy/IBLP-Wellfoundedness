import IBLP.Realization.BoundedRealization
import IBLP.Realization.MarkCertificateFormula

namespace IBLP
open FullMarkedBLP FirstOrder Language
universe u

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData stage a)

/-- All parameters are actual sets in M. The history graph is constructed
from precisely the finite factors of this trace. -/
noncomputable def markFormulaParameters (r : FiniteRowIndex a)
    {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) :
    Fin 5 → stage.model.Element :=
  ![D.graph r,
    h.internalCompositeGraph D.toFiniteTraceRows.toInternalTraceRows (D.graphs_on_trace h),
    stage.hierarchy (D.source r.val),
    stage.hierarchy (h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions),
    stage.hierarchy (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound]

theorem markFormula_realize (r : FiniteRowIndex a)
    {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) :
    modelWeakAgreementFormula.Realize (D.markFormulaParameters r h) ↔
      h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val := by
  have represented := D.toFiniteTraceRows.represents_valid r (D.graph r) (D.graph_represents r)
  have semantics := h.markCertificate_formula_realize D.toFiniteTraceRows.toInternalTraceRows
    r.val represented (D.graphs_on_trace h)
  rw [D.toFiniteTraceRows.source_valid r] at semantics
  exact semantics

/-- This equivalence isolates the genuinely finite weak-agreement clause
of each accurate mark; the separate trace computation is kept explicit. -/
theorem markRealized_iff_formula (r : FiniteRowIndex a) (row : Row) (b : Nat) :
    D.MarkRealized r.val row b ↔
      ∃ target trace,
        row.columns[row.columns.idxOf b - row.step]? = some target ∧
        markTrace a r.val b = some trace ∧
        ∃ h : FactorTrace a target b trace.dropLast,
          modelWeakAgreementFormula.Realize (D.markFormulaParameters r h) := by
  simp only [MarkRealized, D.markFormula_realize]

end FiniteBoundedData
end IBLP
