import IBLP.Realization.NativeGraphExact
import IBLP.NativePrefixTrace
import IBLP.TraceBounds
import IBLP.Realization.TraceGraphCongruence
import IBLP.Realization.MarkGraphCongruence
import IBLP.Realization.MarkedRealization

namespace IBLP
open FullMarkedBLP
universe u

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
  (sourcesRun : IBLP.nativeSources a r.val = some sources) (proper : IBLP.ProperMarks a)
  {b : IBLP.Pattern} (run : IBLP.native a r.val = some (b, sources))

theorem native_prefix_traceGraph {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) (before : start < r.val) :
    D.traceGraph h = (D.nativeData r hr hp he sourcesRun proper run).traceGraph (h.native_prefix run before) := by
  let E := D.nativeData r hr hp he sourcesRun proper run
  apply D.traceGraph_congr_rows E h (h.native_prefix run before)
  have build (xs : List Nat) (pointwise : ∀ i ∈ xs, D.RowGraphsEqual E i i) :
      List.Forall₂ (D.RowGraphsEqual E) xs xs := by
    induction xs with
    | nil => constructor
    | cons i xs ih =>
      exact .cons (pointwise i (by simp)) (ih (fun k hk => pointwise k (List.mem_cons_of_mem i hk)))
  apply build
  intro i member oldValid newValid
  have bound := h.member_le_start i member
  exact (D.nativeData_graph_prefix r hr hp he sourcesRun proper run ⟨i, newValid⟩ (by change i < r.val; omega)).symm

theorem native_prefix_markCertificate (i : FiniteRowIndex a) (k : FiniteRowIndex b)
    (owner : k.val = i.val) (carrierBefore : i.val < r.val)
    {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) (before : start < r.val) :
    h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows i.val ↔
      (h.native_prefix run before).MarkCertificate
        (D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows k.val := by
  have carrier : D.graph i = (D.nativeData r hr hp he sourcesRun proper run).graph k := by
    have exactGraph := D.nativeData_graph_prefix r hr hp he sourcesRun proper run k (by omega)
    have same : (⟨k.val, k.property.1, (by have := r.property.2; omega : k.val ≤ a.length)⟩ : FiniteRowIndex a) = i :=
      Subtype.ext owner
    simpa only [same] using exactGraph.symm
  exact D.markCertificate_congr_graphs (D.nativeData r hr hp he sourcesRun proper run) i k h
    (h.native_prefix run before) carrier (D.native_prefix_traceGraph r hr hp he sourcesRun proper run h before)

end FiniteBoundedData

namespace MarkedRealization
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- Every actual mark of a retained native prefix keeps its complete
accurate history graph and its weak certificate on the whole natural bound. -/
theorem native_prefix_markRealized (r : FiniteRowIndex a) {baseRow oldRow : IBLP.Row} {p e i mark : Nat}
    {sources : List Nat} {b : IBLP.Pattern}
    (hr : IBLP.rowAt a r.val = some baseRow) (hp : baseRow.p = some p) (he : baseRow.e = some e)
    (sourcesRun : IBLP.nativeSources a r.val = some sources) (run : IBLP.native a r.val = some (b, sources))
    (atOld : IBLP.rowAt a i = some oldRow) (before : i < r.val) (marked : mark ∈ oldRow.marks) :
    (R.data.nativeData r hr hp he sourcesRun R.proper run).MarkRealized i oldRow mark := by
  obtain ⟨source, trace, paired, computed, factors, certificate⟩ := R.marks i oldRow mark atOld marked
  have below := IBLP.Row.properMark_lt (R.data.valid _ _ atOld) (R.proper oldRow (rowAt_mem atOld) mark marked)
  have markBefore : mark < r.val := by omega
  have atNew := (IBLP.native_prefix_rowAt run before).trans atOld
  let oldIndex : FiniteRowIndex a := ⟨i, rowAt_pos atOld, rowAt_le_length atOld⟩
  let newIndex : FiniteRowIndex b := ⟨i, rowAt_pos atNew, rowAt_le_length atNew⟩
  refine ⟨source, trace, paired, IBLP.native_prefix_markTrace run before atOld below paired computed,
    factors.native_prefix run markBefore, ?_⟩
  exact (R.data.native_prefix_markCertificate r hr hp he sourcesRun R.proper run
    oldIndex newIndex rfl before factors markBefore).mp certificate

end MarkedRealization
end IBLP
