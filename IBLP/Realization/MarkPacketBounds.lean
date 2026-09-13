import IBLP.Realization.NextSourceBound
import IBLP.Model.AgreementOrdinals

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem markCertificate_rho_min (r : FiniteRowIndex a) {target mark : Nat} {rows : List Nat}
    (h : FactorTrace a target mark rows) (certificate : h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val)
    (eta : Ordinal.{u}) :
    (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).rho eta =
      min (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound (stage.rho (D.map r) eta) := by
  have agreement := (h.markCertificate_iff_allInputs D.toFiniteTraceRows.toInternalTraceRows r.val).mp certificate
  rw [D.toFiniteTraceRows.action_valid r] at agreement
  exact stage.allInputAgreement_rho_min agreement (fun eta => stage.weakAction_ordinal (D.map r) eta)
    (fun eta => h.ordinal_action D.toFiniteTraceRows.toInternalTraceRows.actions eta) eta

/-- Manuscript (7.5): the full input endpoint of the accurate mark word
lies below the next source column, using the actual weak certificate and
next row edge. No packet-capacity hypothesis is used here. -/
theorem mark_next_source_covers_input (r : FiniteRowIndex a) {row : IBLP.Row}
    {target mark source : Nat} {rows : List Nat} (hr : IBLP.rowAt a r.val = some row)
    (proper : row.ProperMark mark) (sourceAt : row.columns[row.columns.idxOf mark + 1 - row.step]? = some source)
    (h : FactorTrace a target mark rows) (certificate : h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val) :
    h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions ≤ D.point source := by
  have targetBound := D.mark_bound_le_next_source_image r hr proper sourceAt h
  rw [D.toFiniteTraceRows.action_valid r] at targetBound
  change (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound ≤ stage.rho (D.map r) (D.point source) at targetBound
  have clipped := D.markCertificate_rho_min r h certificate (D.point source)
  rw [min_eq_left targetBound] at clipped
  by_contra notBelow
  have below := lt_of_not_ge notBelow
  have strict := h.strict_on_input D.toFiniteTraceRows.toInternalTraceRows.actions below.le
    (show h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions ≤ h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions from le_rfl) below
  rw [clipped, h.rho_inputBound] at strict
  exact (lt_irrefl _ strict)

/-- Manuscript (7.6) at every ordinal input whose word image is below the
natural bound: clipped weak agreement gives the exact carrier image. -/
theorem mark_word_image_exact (r : FiniteRowIndex a) {target mark : Nat} {rows : List Nat}
    (h : FactorTrace a target mark rows) (certificate : h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val)
    (eta : Ordinal.{u}) (below : (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).rho eta <
      (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound) :
    stage.rho (D.map r) eta = (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).rho eta := by
  have clipped := D.markCertificate_rho_min r h certificate eta
  have notAbove : ¬ (h.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound ≤ stage.rho (D.map r) eta := by
    intro above
    rw [min_eq_left above] at clipped
    exact below.ne clipped
  rw [min_eq_right (lt_of_not_ge notAbove).le] at clipped
  exact clipped.symm

end IBLP.FiniteBoundedData
