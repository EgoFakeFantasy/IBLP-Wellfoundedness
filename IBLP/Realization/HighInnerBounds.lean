import IBLP.Realization.ControlAction

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

/-- Both inner natural-bound estimates of (5.7) are derived from the
actual control mark and the exact retained trace graphs. -/
theorem highCopy_inner_bounds (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target boundary imageBoundary : Nat} {bridge suffix : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (control : FactorTrace a boundary imageBoundary bridge) (after : FactorTrace a target boundary suffix)
    (old : imageBoundary < a.length)
    (certificate : control.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows a.length) :
    let copied := D.rawCopyData nonempty proper copy hlast hm hp
    let T := (IBLP.rawCopy_factorTrace_old copy control old).word copied.toFiniteTraceRows.toInternalTraceRows.actions
    let V := (IBLP.rawCopy_factorTrace_old copy after (control.target_lt.trans old)).word
      copied.toFiniteTraceRows.toInternalTraceRows.actions
    (T.comp V).bound ≤ stage.ordinalImage (D.lastExtension nonempty).embedding
        (after.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound ∧
      (T.comp V).bound ≤ (control.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound := by
  let copied := D.rawCopyData nonempty proper copy hlast hm hp
  let retainedT := IBLP.rawCopy_factorTrace_old copy control old
  let retainedV := IBLP.rawCopy_factorTrace_old copy after (control.target_lt.trans old)
  have boundV := D.rawCopy_traceBounds_old nonempty proper copy hlast hm hp after (control.target_lt.trans old)
  have boundT := D.rawCopy_traceBounds_old nonempty proper copy hlast hm hp control old
  have rhoT := D.traceRho_congr_values copied control retainedT
    (D.rawCopy_traceGraph_old nonempty proper copy hlast hm hp control old)
    (after.word D.toFiniteTraceRows.toInternalTraceRows.actions).bound
  constructor
  · change (retainedT.word copied.toFiniteTraceRows.toInternalTraceRows.actions).rho
      (retainedV.word copied.toFiniteTraceRows.toInternalTraceRows.actions).bound ≤ _
    rw [← boundV, ← rhoT]
    exact D.control_trace_rho_le_image nonempty control certificate _
  · exact ((retainedT.word copied.toFiniteTraceRows.toInternalTraceRows.actions).rho_le_bound _).trans_eq boundT.symm

end IBLP.FiniteBoundedData
