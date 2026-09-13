import IBLP.CopyMarkCases
import IBLP.Realization.FullCopyRealized
import IBLP.Realization.LowCopyRealized
import IBLP.Realization.HighCopyRealized

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- Every mark actually stored on a copied row has a complete new weak
certificate. All three original filter branches are covered exhaustively. -/
theorem copied_markRealized (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r imageMark : Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (carrierTail : p ≤ r) (rowCopy : IBLP.copyRow a last r = some copied)
    (marked : imageMark ∈ copied.marks) :
    (R.data.rawCopyData nonempty R.proper copy hlast hm hp).MarkRealized
      (r + (a.length - p)) copied imageMark := by
  obtain ⟨mark, oldMarked, _, kept, image⟩ := FiniteBoundedData.copyRow_mark_origin hr rowCopy marked
  obtain ⟨trace, bottom, computed, bottomAt, branch⟩ := IBLP.keepCopiedMark_cases hm hp kept
  rcases branch with full | ⟨crossing, boundary, found, low | ⟨high, imageBoundary, boundaryImage⟩⟩
  · obtain ⟨otherMark, otherImage, _, certificate⟩ :=
      R.fullCopy_markRealized nonempty copy hlast hm hp hr rowCopy oldMarked computed bottomAt full
    have same : otherMark = imageMark := Option.some.inj (otherImage.symm.trans image)
    exact same ▸ certificate
  · obtain ⟨otherMark, otherImage, _, certificate⟩ :=
      R.lowCopy_markRealized nonempty copy hlast hm hp hr carrierTail rowCopy oldMarked computed bottomAt crossing found low
    have same : otherMark = imageMark := Option.some.inj (otherImage.symm.trans image)
    exact same ▸ certificate
  · exact (R.highCopy_markRealized nonempty copy hlast hm hp hr carrierTail rowCopy oldMarked computed bottomAt
      crossing found high boundaryImage image kept).2

end IBLP.MarkedRealization
