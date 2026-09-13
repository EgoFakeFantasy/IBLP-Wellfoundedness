import IBLP.NativeTraceShift
import IBLP.Realization.ShiftRowData
import IBLP.MappedIndices

namespace IBLP

theorem native_suffix_pair {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    (proper : ProperMarks a) {r i mark source : Nat} {row : Row} {sources : List Nat}
    (run : native a r = some (b, sources)) (hr : rowAt a i = some row) (after : r < i)
    (markProper : row.ProperMark mark) (paired : row.columns[row.columns.idxOf mark - row.step]? = some source) :
    (row.shiftAfter r sources.length).columns[
      (row.shiftAfter r sources.length).columns.idxOf (shiftAfter r sources.length mark) - row.step]? =
      some (shiftAfter r sources.length source) := by
  have atNew : rowAt b (i + sources.length) = some (row.shiftAfter r sources.length) := by
    rw [native_suffix_rowAt run after, hr]; rfl
  have newValid := native_preserves_basic valid shapes proper run _ _ atNew
  have mapped := mapped_total (shiftAfter r sources.length) row.columns
  have member := (Row.properMark_indices (valid _ _ hr) markProper).1
  have index := mapped_idxOf mapped newValid.1 member rfl
  change (row.shiftAfter r sources.length).columns.idxOf (shiftAfter r sources.length mark) = row.columns.idxOf mark at index
  change (row.columns.map (shiftAfter r sources.length))[_ - row.step]? = _
  rw [index, List.getElem?_map, paired]
  rfl

theorem native_suffix_markTrace {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    (proper : ProperMarks a) {r i mark source : Nat} {row : Row} {sources rows : List Nat}
    (run : native a r = some (b, sources)) (hr : rowAt a i = some row) (after : r < i)
    (markProper : row.ProperMark mark) (paired : row.columns[row.columns.idxOf mark - row.step]? = some source)
    (h : FactorTrace a source mark rows) :
    markTrace b (i + sources.length) (shiftAfter r sources.length mark) =
      some (rows.map (shiftAfter r sources.length) ++ [shiftAfter r sources.length source]) := by
  have atNew : rowAt b (i + sources.length) = some (row.shiftAfter r sources.length) := by
    rw [native_suffix_rowAt run after, hr]; rfl
  have newValid := native_preserves_basic valid shapes proper run _ _ atNew
  have newProper := Row.shiftAfter_properMark markProper r sources.length
  obtain ⟨member, index, _⟩ := Row.properMark_indices newValid newProper
  have newPaired := native_suffix_pair valid shapes proper run hr after markProper paired
  change (row.shiftAfter r sources.length).columns[
    (row.shiftAfter r sources.length).columns.idxOf (shiftAfter r sources.length mark) -
      (row.shiftAfter r sources.length).step]? = some (shiftAfter r sources.length source) at newPaired
  have computed := traceFrom_iff.mpr (h.native_shift valid shapes run).toTrace
  have legal : (row.shiftAfter r sources.length).step ≤
      (row.shiftAfter r sources.length).columns.idxOf (shiftAfter r sources.length mark) := by omega
  simp only [markTrace, atNew, Bind.bind, Option.bind, if_pos member, if_pos legal, newPaired, computed]

end IBLP
