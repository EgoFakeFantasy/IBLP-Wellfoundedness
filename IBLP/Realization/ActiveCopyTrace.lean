import IBLP.Realization.CopiedBottom

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

include R in
/-- If a stored copied mark has its bottom in the new tail, it must have
come from the full-copy branch. Every nonterminal factor is then the same
uniform translated image, between the new block start and its carrier. -/
theorem copied_active_factors (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r imageMark newBottom : Nat} {newTrace : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (carrierTail : p ≤ r) (rowCopy : IBLP.copyRow a last r = some copied)
    (marked : imageMark ∈ copied.marks)
    (computed : IBLP.markTrace b (r + (a.length - p)) imageMark = some newTrace)
    (bottomAt : IBLP.fromRight newTrace 2 = some newBottom) (active : a.length ≤ newBottom) :
    ∃ mark trace, mark ∈ row.marks ∧ IBLP.markTrace a r mark = some trace ∧
      newTrace.dropLast = trace.dropLast.map (· + (a.length - p)) ∧
      (∀ t ∈ trace.dropLast, p ≤ t ∧ t < r) ∧
      ∀ t ∈ newTrace.dropLast, a.length ≤ t ∧ t < r + (a.length - p) := by
  obtain ⟨mark, trace, bottom, actualTrace, oldMarked, markImage, oldComputed, oldBottom, newComputed, newBottomAt⟩ :=
    R.copied_mark_bottom_origin nonempty copy hlast hm hp hr carrierTail rowCopy marked
  have sameTrace : actualTrace = newTrace := Option.some.inj (newComputed.symm.trans computed)
  subst actualTrace
  have bottomValue := Option.some.inj (newBottomAt.symm.trans bottomAt)
  have pn : p ≤ a.length := carrierTail.trans (rowAt_le_length hr)
  have full : p ≤ bottom := by
    by_contra outside
    simp only [if_neg outside] at bottomValue
    omega
  obtain ⟨source, target, paired, _, _, expected⟩ :=
    R.fullCopy_trace_from_bottom nonempty copy hlast hm hp hr rowCopy oldMarked oldComputed oldBottom full markImage
  have traceValue := Option.some.inj (computed.symm.trans expected)
  have factorsValue : newTrace.dropLast = trace.dropLast.map (· + (a.length - p)) := by
    rw [traceValue, List.dropLast_concat]
  obtain ⟨oldSource, history, oldPaired, historyAt, factors, _⟩ := R.marks r row mark hr oldMarked
  have sameHistory : history = trace := Option.some.inj (historyAt.symm.trans oldComputed)
  subst history
  have oldShape := (IBLP.markTrace_spec hr oldPaired oldComputed).2.2.unique factors.toTrace
  have tail := factors.tail_of_bottom (by rw [← oldShape]; exact oldBottom) full
  have markBelow := IBLP.Row.properMark_lt (R.data.valid _ _ hr) (R.proper row (rowAt_mem hr) mark oldMarked)
  have oldBounds : ∀ t ∈ trace.dropLast, p ≤ t ∧ t < r := by
    intro t member
    exact ⟨tail t member, (factors.member_le_start t member).trans_lt markBelow⟩
  refine ⟨mark, trace, oldMarked, oldComputed, factorsValue, oldBounds, ?_⟩
  intro t member
  rw [factorsValue] at member
  obtain ⟨old, oldMember, value⟩ := List.mem_map.mp member
  have bounds := oldBounds old oldMember
  omega

end IBLP.MarkedRealization
