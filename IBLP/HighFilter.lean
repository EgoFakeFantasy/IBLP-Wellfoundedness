import IBLP.CrossingIndices

namespace IBLP

/-- The literal next-source-column test in the high branch forces that
source and its predecessor source below the minimum. It also supplies the
actual control mark used for the inserted bridge. -/
theorem keepCopiedMark_high_spec {a : Pattern} {last row : Row} {cols trace : List Nat}
    {minimum p r mark imageMark bottom boundary imageBoundary source : Nat}
    (lastValid : last.BasicValid a.length) (lastShape : last.OrdinaryShape)
    (valid : row.BasicValid r) (proper : row.ProperMark mark)
    (mapped : FullMarkedBLP.MapsEntries (copyEntry a.length last) row.columns cols)
    (sorted : cols.Pairwise (· < ·)) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (computed : markTrace a r mark = some trace) (bottomAt : fromRight trace 2 = some bottom)
    (crossing : bottom < p) (found : trace.find? (· < p) = some boundary) (high : minimum ≤ boundary)
    (boundaryImage : copyEntry a.length last boundary = some imageBoundary)
    (markImage : copyEntry a.length last mark = some imageMark)
    (paired : row.columns[row.columns.idxOf mark - row.step]? = some source)
    (kept : keepCopiedMark a last r row cols mark = true) :
    imageBoundary ∈ last.marks ∧ source < minimum ∧
      ∃ next imageNext, row.columns[row.columns.idxOf mark + 1 - row.step]? = some next ∧
        copyEntry a.length last next = some imageNext ∧ imageNext ≤ minimum ∧ next < minimum := by
  have indices := Row.properMark_indices valid proper
  have index := mapped_idxOf mapped sorted indices.1 markImage
  have legal : row.step ≤ row.columns.idxOf mark + 1 := by omega
  obtain ⟨next, nextAt, sourceLess⟩ := Row.next_source_exists valid proper paired
  obtain ⟨imageNext, imageNextAt, nextImage⟩ := mapped.at_left nextAt
  have parsed : (if imageBoundary ∈ last.marks then
      (cols[row.columns.idxOf mark + 1 - row.step]?).any (· ≤ minimum) else false) = true := by
    simpa [keepCopiedMark, hm, hp, computed, bottomAt, show ¬p ≤ bottom by omega,
      found, show ¬boundary < minimum by omega, boundaryImage, markImage, index, legal] using kept
  by_cases member : imageBoundary ∈ last.marks
  · have nextBound : imageNext ≤ minimum := by simpa [member, imageNextAt] using parsed
    have nextLow := copyEntry_below_minimum_of_image_le lastValid lastShape hm hp nextImage nextBound
    exact ⟨member, sourceLess.trans nextLow, next, imageNext, nextAt, nextImage, nextBound, nextLow⟩
  · simp [member] at parsed

end IBLP
