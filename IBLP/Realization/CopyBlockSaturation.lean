import IBLP.BlockSaturation
import IBLP.Realization.CopyPredecessor
import IBLP.Realization.NextCopy

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

include D in
/-- Conditional saturation is transported to the new copied block. A
predecessor in that block must itself come from the translated source tail;
the source endpoint and its q row therefore have actual copied origins. -/
theorem rawCopy_block_saturated (proper : IBLP.ProperMarks a) {b : IBLP.Pattern}
    {last : IBLP.Row} {minimum p : Nat} (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum)
    (hp : last.p = some p) (saturated : IBLP.BlockSaturated a p a.length) :
    IBLP.BlockSaturated b a.length b.length := by
  have lastAt := IBLP.getLast_rowAt hlast
  have nonempty := IBLP.rowAt_pos lastAt
  have controlPred : IBLP.predecessor a a.length = some p := by
    simp [IBLP.predecessor, lastAt, hp]
  have pn := IBLP.predecessor_lt D.valid D.shapes controlPred
  have geometry := D.rawCopy_geometry proper copy
  have length := IBLP.rawCopy_length copy hlast hp
  intro r row v e q before inBlock atRow hv he hq
  have pred : IBLP.predecessor b r = some v := by simp [IBLP.predecessor, atRow, hv]
  have vr := IBLP.predecessor_lt geometry.1 geometry.2.1 pred
  obtain ⟨source, sourceLower, _, owner, rowCopy⟩ :=
    IBLP.rawCopy_row_origin copy hlast hp (inBlock.trans vr.le) atRow
  obtain ⟨original, originalAt, _⟩ := Option.bind_eq_some_iff.mp rowCopy
  have sourceUpper : source < a.length := by omega
  obtain ⟨mapped, _, step⟩ := D.copyRow_columns nonempty lastAt hm hp originalAt rowCopy
  obtain ⟨oldV, oldPred, predImage⟩ := IBLP.mapped_fromRight mapped
    (show IBLP.fromRight row.columns (original.step + 1) = some v by simpa only [IBLP.Row.p, step] using hv)
  have pImage : IBLP.copyEntry a.length last p = some a.length := by
    simpa only [Nat.add_sub_of_le pn.le] using
      IBLP.copyEntry_tail (D.valid _ _ lastAt) hm hp (show p ≤ p from le_rfl)
  have oldInBlock : p ≤ oldV := by
    by_contra outside
    have less := D.copyEntry_strict nonempty lastAt hm hp (by omega) (by omega : oldV < p) predImage pImage
    omega
  obtain ⟨oldE, oldEnd, endImage⟩ := IBLP.mapped_fromRight mapped
    (show IBLP.fromRight row.columns original.step = some e by simpa only [IBLP.Row.e, step] using he)
  have ve := IBLP.Row.predecessor_lt_endpoint (D.valid _ _ originalAt) oldPred oldEnd
  have es := IBLP.fromRight_le_last (D.valid _ _ originalAt).1 (D.valid _ _ originalAt).2.2.1
    (IBLP.Row.step_pos (D.shapes original (rowAt_mem originalAt))) oldEnd
  have translatedEnd := IBLP.copyEntry_tail (D.valid _ _ lastAt) hm hp (oldInBlock.trans ve.le)
  have endValue : e = oldE + (a.length - p) := Option.some.inj (endImage.symm.trans translatedEnd)
  obtain ⟨oldEndRow, oldEndAt⟩ := IBLP.rowAt_exists (by omega : 0 < oldE) (by omega : oldE ≤ a.length)
  obtain ⟨endRow, atEndRow, endCopy⟩ := IBLP.rawCopy_row_image copy hlast hp (by omega : p ≤ oldE) (by omega)
  have mappedEnd := (D.copyRow_columns nonempty lastAt hm hp oldEndAt endCopy).1
  have newQ : endRow.q = some q := by
    simpa only [IBLP.penultimate, endValue, atEndRow, Option.bind_some] using hq
  obtain ⟨oldQ, oldQAt, qImage⟩ := IBLP.mapped_fromRight mappedEnd newQ
  have oldQValue : IBLP.penultimate a oldE = some oldQ := by
    simpa only [IBLP.penultimate, oldEndAt, Option.bind_some, IBLP.Row.q] using oldQAt
  have oldSat := saturated source original oldV oldE oldQ sourceUpper oldInBlock originalAt oldPred oldEnd oldQValue
  rcases oldSat.eq_or_lt with equal | less
  · subst oldQ
    exact (Option.some.inj (qImage.symm.trans predImage)).le
  · have oldVBound := IBLP.Row.column_le_last (D.valid _ _ originalAt) (IBLP.fromRight_mem oldPred)
    exact (D.copyEntry_strict nonempty lastAt hm hp (by omega) less qImage predImage).le

end IBLP.FiniteBoundedData
