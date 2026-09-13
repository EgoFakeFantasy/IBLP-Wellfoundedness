import IBLP.Realization.NativeSuffixMarks
import IBLP.NativeTopMarkPairs

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
  (sourcesRun : IBLP.nativeSources a r.val = some sources) (proper : IBLP.ProperMarks a)
  {b : IBLP.Pattern} (run : IBLP.native a r.val = some (b, sources))

/-- A paired source retains its accurate history and weak equality with
the original base graph. Each actual carrier restriction is applied later. -/
def nativeMarkPayload (mark source : Nat) : Prop := ∃ rows, ∃ h : FactorTrace b source mark rows,
    CutAction.AllInputAgreement (D.toFiniteTraceRows.toInternalTraceRows.actions.action r.val)
      (h.word (D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows.actions)
      (h.word (D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows.actions).bound

theorem nativeMarkPayload_old {source mark : Nat} {rows : List Nat}
    (h : FactorTrace a source mark rows) (before : mark < r.val)
    (certificate : h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val) :
    D.nativeMarkPayload r hr hp he sourcesRun proper run mark source := by
  let E := D.nativeData r hr hp he sourcesRun proper run
  let history := h.native_prefix run before
  refine ⟨rows, history, ?_⟩
  have graphs := D.native_prefix_traceGraph r hr hp he sourcesRun proper run h before
  have actions := D.traceAction_congr_graphs E h history graphs
  rw [← actions]
  exact (h.markCertificate_iff_allInputs D.toFiniteTraceRows.toInternalTraceRows r.val).mp certificate

theorem nativeMarkPayload_direct (j : Nat) (bound : j < sources.length) :
    ∃ source, IBLP.predecessor b (r.val + j) = some source ∧
      D.nativeMarkPayload r hr hp he sourcesRun proper run (r.val + j) source := by
  let E := D.nativeData r hr hp he sourcesRun proper run
  have length := IBLP.native_length run
  obtain ⟨out, atOut⟩ := IBLP.rowAt_exists (a := b) (r := r.val + j)
    (by have := r.property.1; omega) (by have := r.property.2; omega)
  have shape := E.shapes out (rowAt_mem atOut)
  obtain ⟨source, atSource⟩ := IBLP.fromRight_exists (xs := out.columns) (k := out.step + 1)
    (by omega) (by have := IBLP.Row.step_lt_length shape; omega)
  have pred : IBLP.predecessor b (r.val + j) = some source := by simp [IBLP.predecessor, atOut, IBLP.Row.p, atSource]
  have less := IBLP.predecessor_lt E.valid E.shapes pred
  let i : FiniteRowIndex b := ⟨r.val + j, rowAt_pos atOut, rowAt_le_length atOut⟩
  have restriction := D.nativeData_family_restriction r hr hp he sourcesRun proper run i
    (by change r.val ≤ r.val + j; omega) (by change r.val + j ≤ r.val + sources.length; omega)
  refine ⟨source, pred, [r.val + j], FactorTrace.single pred less, ?_⟩
  change CutAction.AllInputAgreement (D.toFiniteTraceRows.toInternalTraceRows.actions.action r.val)
    (E.toFiniteTraceRows.toInternalTraceRows.actions.action i.val)
    (E.toFiniteTraceRows.toInternalTraceRows.actions.action i.val).bound
  intro z
  rw [restriction.act_eq, stage.cutSpace.cut_cut, min_self]

theorem nativeMarkPayload_certificate {mark source : Nat} {rows : List Nat}
    (history : FactorTrace b source mark rows)
    (agreement : CutAction.AllInputAgreement (D.toFiniteTraceRows.toInternalTraceRows.actions.action r.val)
      (history.word (D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows.actions)
      (history.word (D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows.actions).bound)
    (i : FiniteRowIndex b) (lower : r.val ≤ i.val) (upper : i.val ≤ r.val + sources.length)
    (before : mark < i.val) :
    history.MarkCertificate (D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows i.val := by
  let E := D.nativeData r hr hp he sourcesRun proper run
  have restriction := D.nativeData_family_restriction r hr hp he sourcesRun proper run i lower upper
  have bounds := history.carrier_bound E.toFiniteTraceRows.toInternalTraceRows E.point_increasing i.property.2 before
  have fits : (history.word E.toFiniteTraceRows.toInternalTraceRows.actions).bound ≤
      (E.toFiniteTraceRows.toInternalTraceRows.actions.action i.val).bound := by
    rw [E.toFiniteTraceRows.action_valid]
    exact bounds.2.1.trans bounds.2.2.le
  exact (history.markCertificate_iff_allInputs E.toFiniteTraceRows.toInternalTraceRows i.val).mpr
    (restriction.agreement (CutRestriction.refl _) agreement le_rfl fits le_rfl)

end IBLP.FiniteBoundedData
