import IBLP.Realization.CopyRowGeometry
import IBLP.Realization.CopyTrace
import IBLP.MappedIndices

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

include D in
/-- Any proved new factor chain at the actual point images yields the
algorithm's markTrace, with exactly the mapped paired-source array entry. -/
theorem copied_markTrace (nonempty : 0 < a.length) {b : IBLP.Pattern}
    {last row copied : IBLP.Row} {minimum p r mark imageMark target imageTarget : Nat} {rows : List Nat}
    (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (hr : rowAt a r = some row) (carrierTail : p ≤ r) (rowCopy : IBLP.copyRow a last r = some copied)
    (proper : row.ProperMark mark) (markImage : IBLP.copyEntry a.length last mark = some imageMark)
    (paired : row.columns[row.columns.idxOf mark - row.step]? = some target)
    (targetImage : IBLP.copyEntry a.length last target = some imageTarget)
    (factors : FactorTrace b imageTarget imageMark rows) :
    copied.columns[copied.columns.idxOf imageMark - copied.step]? = some imageTarget ∧
      IBLP.markTrace b (r + (a.length - p)) imageMark = some (rows ++ [imageTarget]) := by
  have properIndices := IBLP.Row.properMark_indices (D.valid _ _ hr) proper
  obtain ⟨mapped, sorted, step⟩ := D.copyRow_columns nonempty (IBLP.getLast_rowAt hlast) hm hp hr rowCopy
  have index := IBLP.mapped_idxOf mapped sorted properIndices.1 markImage
  have member : imageMark ∈ copied.columns := by
    obtain ⟨value, hv, valueImage⟩ := IBLP.mapped_mem_left mapped properIndices.1
    have same := Option.some.inj (valueImage.symm.trans markImage)
    exact same ▸ hv
  have legal : copied.step ≤ copied.columns.idxOf imageMark := by rw [step, index]; omega
  obtain ⟨otherTarget, atTarget, otherImage⟩ := mapped.at_left paired
  have sameTarget := Option.some.inj (otherImage.symm.trans targetImage)
  have newPaired : copied.columns[copied.columns.idxOf imageMark - copied.step]? = some imageTarget := by
    rw [index, step]
    exact atTarget.trans (congrArg some sameTarget)
  obtain ⟨actual, atActual, actualCopy⟩ := IBLP.rawCopy_row_image copy hlast hp carrierTail (rowAt_le_length hr)
  have sameRow : actual = copied := Option.some.inj (actualCopy.symm.trans rowCopy)
  subst actual
  exact ⟨newPaired, by simp [IBLP.markTrace, atActual, member, legal, newPaired, IBLP.traceFrom_iff.mpr factors.toTrace]⟩

end IBLP.FiniteBoundedData
