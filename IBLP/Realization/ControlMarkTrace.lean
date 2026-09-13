import IBLP.CrossingIndices
import IBLP.Realization.MarkedRealization
import IBLP.RawCopy

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- The bridge used by high crossing comes from an actual existing
control-row mark; its paired source is recovered from the explicit step. -/
theorem control_mark_trace {last : IBLP.Row} {minimum p boundary imageBoundary : Nat}
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (high : minimum ≤ boundary) (below : boundary < p)
    (image : IBLP.copyEntry a.length last boundary = some imageBoundary) (marked : imageBoundary ∈ last.marks) :
    ∃ trace, IBLP.markTrace a a.length imageBoundary = some trace ∧ imageBoundary < a.length ∧
      ∃ h : FactorTrace a boundary imageBoundary trace.dropLast,
        h.MarkCertificate R.data.toFiniteTraceRows.toInternalTraceRows a.length := by
  have hr := IBLP.getLast_rowAt hlast
  have paired := IBLP.copyEntry_high_paired (R.data.valid _ _ hr) hm hp high below image
  obtain ⟨target, trace, oldPaired, computed, factors, certificate⟩ := R.marks a.length last imageBoundary hr marked
  have same : target = boundary := Option.some.inj (oldPaired.symm.trans paired)
  subst target
  exact ⟨trace, computed, IBLP.Row.properMark_lt (R.data.valid _ _ hr)
    (R.proper last (rowAt_mem hr) imageBoundary marked), factors, certificate⟩

end IBLP.MarkedRealization
