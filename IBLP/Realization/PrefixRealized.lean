import IBLP.Realization.PrefixData
import IBLP.Realization.MarkedRealization
import IBLP.Realization.TraceGraphCongruence
import IBLP.Realization.MarkGraphCongruence

namespace IBLP
open FullMarkedBLP
universe u

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem take_traceGraph (k : Nat) {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) (bound : start ≤ k) :
    D.traceGraph h = (D.takeData k).traceGraph (h.take bound) := by
  apply D.traceGraph_congr_rows (D.takeData k) h (h.take bound)
  have matched (xs : List Nat) : List.Forall₂ (D.RowGraphsEqual (D.takeData k)) xs xs := by
    induction xs with
    | nil => constructor
    | cons r rs ih => exact .cons (fun _ _ => rfl) ih
  exact matched rows

theorem take_markCertificate (k : Nat) (r : FiniteRowIndex (a.take k))
    {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) (bound : start ≤ k) :
    h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r.val ↔
      (h.take bound).MarkCertificate (D.takeData k).toFiniteTraceRows.toInternalTraceRows r.val :=
  D.markCertificate_congr_graphs (D.takeData k) (takeRowIndex k r) r h (h.take bound)
    rfl (D.take_traceGraph k h bound)

end FiniteBoundedData

namespace MarkedRealization
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- Proper marks never use a factor outside the retained prefix. The exact
algorithmic histories and the entire composite graphs therefore survive. -/
noncomputable def take (k : Nat) : MarkedRealization stage (a.take k) where
  data := R.data.takeData k
  proper := R.proper.take k
  marks := by
    intro r row mark hr marked
    have old := IBLP.take_row_origin hr
    have below := IBLP.Row.properMark_lt (R.data.valid _ _ old) (R.proper row (rowAt_mem old) mark marked)
    have rowBound := rowAt_le_length hr
    have rb : r ≤ k := by simp only [List.length_take] at rowBound; omega
    have mb : mark ≤ k := by omega
    obtain ⟨source, trace, paired, computed, factors, certificate⟩ := R.marks r row mark old marked
    exact ⟨source, trace, paired, IBLP.take_markTrace rb old below paired computed,
      factors.take mb, (R.data.take_markCertificate k ⟨r, rowAt_pos hr, rowBound⟩ factors mb).mp certificate⟩

theorem take_top (k : Nat) : (R.take k).top = R.data.point ((a.take k).length + 1) := rfl

end MarkedRealization

namespace BoundedRealization
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : BoundedRealization stage a)

/-- Saturation, as well as all semantic data, is inherited by every prefix. -/
noncomputable def take (k : Nat) : BoundedRealization stage (a.take k) :=
  (R.toMarkedRealization.take k).withSaturation (R.saturated.take R.data.valid R.data.shapes k)

theorem take_top (k : Nat) : (R.take k).top = R.data.point ((a.take k).length + 1) := rfl

end BoundedRealization
end IBLP
