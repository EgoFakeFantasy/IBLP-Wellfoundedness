import IBLP.RawCopyRows
import IBLP.Realization.RawCopyGraphExact

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

include D in
theorem rawCopy_predecessor_image (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p r t : Nat} (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (tail : p ≤ r) (pred : IBLP.predecessor a r = some t) :
    ∃ image, IBLP.copyEntry a.length last t = some image ∧
      IBLP.predecessor b (r + (a.length - p)) = some image := by
  obtain ⟨row, hr, oldPred⟩ := Option.bind_eq_some_iff.mp pred
  obtain ⟨copied, atCopied, rowCopy⟩ := IBLP.rawCopy_row_image copy hlast hp tail (rowAt_le_length hr)
  obtain ⟨mapped, _, step⟩ := D.copyRow_columns nonempty (IBLP.getLast_rowAt hlast) hm hp hr rowCopy
  obtain ⟨image, atImage, value⟩ := IBLP.mapped_fromRight_left mapped oldPred
  have newPred : copied.p = some image := by simpa only [IBLP.Row.p, step] using atImage
  exact ⟨image, value, by simp [IBLP.predecessor, atCopied, newPred]⟩

include D in
theorem rawCopy_predecessor_tail (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p r t : Nat} (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (tail : p ≤ t) (pred : IBLP.predecessor a r = some t) :
    IBLP.predecessor b (r + (a.length - p)) = some (t + (a.length - p)) := by
  have tr := IBLP.predecessor_lt D.valid D.shapes pred
  obtain ⟨image, value, next⟩ := D.rawCopy_predecessor_image nonempty copy hlast hm hp (by omega) pred
  have expected := IBLP.copyEntry_tail (D.valid _ _ (IBLP.getLast_rowAt hlast)) hm hp tail
  have same := Option.some.inj (value.symm.trans expected)
  exact next.trans (congrArg some same)

end IBLP.FiniteBoundedData
