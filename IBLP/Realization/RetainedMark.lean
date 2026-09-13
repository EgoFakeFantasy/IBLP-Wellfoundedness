import IBLP.Realization.MarkAbsolute
import IBLP.Realization.RawCopyGraphExact
import IBLP.Realization.MarkedRealization
import IBLP.RetainedTrace

namespace IBLP
open FullMarkedBLP
universe u

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem rawCopy_traceGraph_old (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start : Nat} {rows : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (h : FactorTrace a target start rows) (old : start < a.length) :
    (D.traceGraph h).val =
      ((D.rawCopyData nonempty proper copy hlast hm hp).traceGraph (IBLP.rawCopy_factorTrace_old copy h old)).val := by
  let copied := D.rawCopyData nonempty proper copy hlast hm hp
  apply D.traceGraph_congr_values copied h (IBLP.rawCopy_factorTrace_old copy h old)
  have build (xs : List Nat) (pointwise : ∀ r ∈ xs, D.RowGraphValuesEqual copied r r) :
      List.Forall₂ (D.RowGraphValuesEqual copied) xs xs := by
    induction xs with
    | nil => constructor
    | cons r rs ih =>
      exact .cons (pointwise r (by simp)) (ih (fun t ht => pointwise t (List.mem_cons_of_mem r ht)))
  apply build
  intro r hr oldValid newValid
  have below := h.member_le_start r hr
  exact (D.rawCopyData_graph_old nonempty proper copy hlast hm hp ⟨r, newValid⟩ (by dsimp; omega)).symm

theorem rawCopy_markCertificate_old (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p target start : Nat} {rows : List Nat}
    (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (r : FiniteRowIndex a) (s : FiniteRowIndex b) (owner : s.val = r.val) (carrierOld : r.val < a.length)
    (h : FactorTrace a target start rows) (old : start < a.length) :
    h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val ↔
      (IBLP.rawCopy_factorTrace_old copy h old).MarkCertificate
        (D.rawCopyData nonempty proper copy hlast hm hp).toFiniteTraceRows.toInternalTraceRows s.val := by
  have carrier : (D.graph r).val = ((D.rawCopyData nonempty proper copy hlast hm hp).graph s).val := by
    have exactGraph := D.rawCopyData_graph_old nonempty proper copy hlast hm hp s (by omega)
    have same : (⟨s.val, s.property.1, (by omega : s.val ≤ a.length)⟩ : FiniteRowIndex a) = r :=
      Subtype.ext owner
    simpa only [same] using exactGraph.symm
  exact D.markCertificate_absolute (D.rawCopyData nonempty proper copy hlast hm hp) r s h
    (IBLP.rawCopy_factorTrace_old copy h old) carrier
    (D.rawCopy_traceGraph_old nonempty proper copy hlast hm hp h old)
    (fun rho below => ((D.lastExtension nonempty).hierarchy_below rho below).symm)

end FiniteBoundedData

namespace MarkedRealization
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- Every mark on the retained prefix keeps its original accurate trace
and full weak certificate in the next model. -/
theorem rawCopy_markRealized_old (nonempty : 0 < a.length) {b : IBLP.Pattern} {last row : IBLP.Row}
    {minimum p r mark : Nat} (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (old : r < a.length) (marked : mark ∈ row.marks) :
    (R.data.rawCopyData nonempty R.proper copy hlast hm hp).MarkRealized r row mark := by
  obtain ⟨source, trace, paired, computed, factors, certificate⟩ := R.marks r row mark hr marked
  have below := IBLP.Row.properMark_lt (R.data.valid _ _ hr) (R.proper row (rowAt_mem hr) mark marked)
  have markOld : mark < a.length := by omega
  have newRow := (IBLP.rawCopy_prefix copy old).trans hr
  let oldIndex : FiniteRowIndex a := ⟨r, rowAt_pos hr, rowAt_le_length hr⟩
  let newIndex : FiniteRowIndex b := ⟨r, rowAt_pos newRow, rowAt_le_length newRow⟩
  refine ⟨source, trace, paired, IBLP.rawCopy_markTrace_old copy old hr below paired computed,
    IBLP.rawCopy_factorTrace_old copy factors markOld, ?_⟩
  exact (R.data.rawCopy_markCertificate_old nonempty R.proper copy hlast hm hp
    oldIndex newIndex rfl old factors markOld).mp certificate

end MarkedRealization
end IBLP
