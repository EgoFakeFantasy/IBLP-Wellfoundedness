import IBLP.MappedIndices
import IBLP.CopyEntry
import IBLP.CopyEntryTotal

namespace IBLP

theorem paired_source_of_explicit_edge {xs : List Nat} {step source target : Nat}
    (sorted : xs.Pairwise (· < ·)) (edge : (source, target) ∈ xs.zip (xs.drop step)) :
    xs[xs.idxOf target - step]? = some source := by
  obtain ⟨i, hi, value⟩ := List.mem_iff_getElem.mp edge
  have atPair : (xs.zip (xs.drop step))[i]? = some (source, target) :=
    List.getElem?_eq_some_iff.mpr ⟨hi, value⟩
  rw [List.getElem?_zip_eq_some, List.getElem?_drop] at atPair
  have index := sorted_idxOf_of_at sorted atPair.2
  rw [index, Nat.add_sub_cancel_left]
  exact atPair.1

/-- In the high branch the image point is an explicit target column of the
control row, and its literal paired-source position is the crossing point. -/
theorem copyEntry_high_paired {n minimum p source image : Nat} {last : Row}
    (valid : last.BasicValid n) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (high : minimum ≤ source) (below : source < p) (copied : copyEntry n last source = some image) :
    last.columns[last.columns.idxOf image - last.step]? = some source := by
  rcases copyEntry_cases hm hp copied with ⟨low, _⟩ | ⟨_, tail, _⟩ | ⟨_, _, edge⟩
  · omega
  · omega
  · exact paired_source_of_explicit_edge valid.1 edge

theorem copyEntry_moves_above_minimum {n minimum p x y : Nat} {last : Row}
    (valid : last.BasicValid n) (shape : last.OrdinaryShape)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (above : minimum ≤ x) (copied : copyEntry n last x = some y) : x < y := by
  have pn : p < n := fromRight_lt_last valid.1 valid.2.2.1 (by have := Row.step_pos shape; omega) hp
  rcases copyEntry_cases hm hp copied with ⟨low, _⟩ | ⟨_, _, translated⟩ | ⟨_, _, edge⟩
  · omega
  · omega
  · exact Row.explicit_edge_increases valid shape edge

theorem copyEntry_below_minimum_of_image_le {n minimum p x y : Nat} {last : Row}
    (valid : last.BasicValid n) (shape : last.OrdinaryShape)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (copied : copyEntry n last x = some y) (below : y ≤ minimum) : x < minimum := by
  by_contra notLow
  have moved := copyEntry_moves_above_minimum valid shape hm hp (by omega : minimum ≤ x) copied
  omega

theorem Row.next_source_exists {row : Row} {r mark source : Nat}
    (valid : row.BasicValid r) (proper : row.ProperMark mark)
    (paired : row.columns[row.columns.idxOf mark - row.step]? = some source) :
    ∃ next, row.columns[row.columns.idxOf mark + 1 - row.step]? = some next ∧ source < next := by
  have indices := Row.properMark_indices valid proper
  have nextBound : row.columns.idxOf mark + 1 - row.step < row.columns.length := by omega
  let next := row.columns[row.columns.idxOf mark + 1 - row.step]
  have nextAt : row.columns[row.columns.idxOf mark + 1 - row.step]? = some next :=
    List.getElem?_eq_some_iff.mpr ⟨nextBound, rfl⟩
  obtain ⟨oldBound, oldValue⟩ := List.getElem?_eq_some_iff.mp paired
  have less := List.pairwise_iff_getElem.mp valid.1 (row.columns.idxOf mark - row.step)
    (row.columns.idxOf mark + 1 - row.step) oldBound nextBound (by omega)
  exact ⟨next, nextAt, by simpa only [oldValue] using less⟩

theorem Row.next_target_edge {row : Row} {r mark source : Nat}
    (valid : row.BasicValid r) (proper : row.ProperMark mark)
    (sourceAt : row.columns[row.columns.idxOf mark + 1 - row.step]? = some source) :
    ∃ target, row.columns[row.columns.idxOf mark + 1]? = some target ∧ mark < target ∧
      (source, target) ∈ row.edgePairs r := by
  have indices := Row.properMark_indices valid proper
  let target := row.columns[row.columns.idxOf mark + 1]
  have targetAt : row.columns[row.columns.idxOf mark + 1]? = some target :=
    List.getElem?_eq_some_iff.mpr ⟨indices.2.2, rfl⟩
  obtain ⟨markBound, markValue⟩ := List.getElem?_eq_some_iff.mp (List.getElem?_idxOf indices.1)
  have less := List.pairwise_iff_getElem.mp valid.1 (row.columns.idxOf mark) (row.columns.idxOf mark + 1)
    markBound indices.2.2 (by omega)
  have alignment : row.step + (row.columns.idxOf mark + 1 - row.step) = row.columns.idxOf mark + 1 := by omega
  have pairAt : (row.columns.zip (row.columns.drop row.step))[row.columns.idxOf mark + 1 - row.step]? =
      some (source, target) := by
    rw [List.getElem?_zip_eq_some, List.getElem?_drop, alignment]
    exact ⟨sourceAt, targetAt⟩
  obtain ⟨pairBound, pairValue⟩ := List.getElem?_eq_some_iff.mp pairAt
  exact ⟨target, targetAt, by simpa only [markValue] using less,
    Row.explicit_edge (List.mem_iff_getElem.mpr ⟨_, pairBound, pairValue⟩)⟩

theorem copied_next_source_index {f : Nat → Option Nat} {row copied : Row}
    {r mark imageMark source imageSource : Nat} (valid : row.BasicValid r) (proper : row.ProperMark mark)
    (mapped : FullMarkedBLP.MapsEntries f row.columns copied.columns) (sorted : copied.columns.Pairwise (· < ·))
    (step : copied.step = row.step) (markImage : f mark = some imageMark)
    (sourceAt : row.columns[row.columns.idxOf mark + 1 - row.step]? = some source)
    (sourceImage : f source = some imageSource) :
    copied.columns[copied.columns.idxOf imageMark + 1 - copied.step]? = some imageSource := by
  have index := mapped_idxOf mapped sorted (Row.properMark_indices valid proper).1 markImage
  rw [index, step]
  obtain ⟨value, atValue, image⟩ := mapped.at_left sourceAt
  exact atValue.trans (congrArg some (Option.some.inj (image.symm.trans sourceImage)))

end IBLP
