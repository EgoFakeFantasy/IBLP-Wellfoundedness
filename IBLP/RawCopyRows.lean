import IBLP.RawCopy

namespace IBLP

theorem rawCopy_row_image {a b : Pattern} {last : Row} {p source : Nat}
    (copy : rawCopy a = some b) (hlast : a.getLast? = some last) (hp : last.p = some p)
    (tail : p ≤ source) (bound : source ≤ a.length) :
    ∃ row, rowAt b (source + (a.length - p)) = some row ∧ copyRow a last source = some row := by
  obtain ⟨last', p', block, hlast', hp', positive, included, hblock, result⟩ := rawCopy_decomposition copy
  have sameLast : last' = last := Option.some.inj (hlast'.symm.trans hlast)
  subst last'
  have sameP : p' = p := Option.some.inj (hp'.symm.trans hp)
  subst p'
  have sourceAt : ((List.range (a.length - p + 1)).map (p + ·))[source - p]? = some source := by
    apply List.getElem?_eq_some_iff.mpr
    refine ⟨by simp only [List.length_map, List.length_range]; omega, ?_⟩
    simp only [List.getElem_map, List.getElem_range, Nat.add_sub_of_le tail]
  obtain ⟨row, atBlock, rowCopy⟩ := (FullMarkedBLP.option_mapM_forall2 hblock).at_left sourceAt
  have prefixLength : (a.take (a.length - 1)).length = a.length - 1 := by simp
  have index : source + (a.length - p) - 1 - (a.take (a.length - 1)).length = source - p := by
    rw [prefixLength]
    omega
  refine ⟨row, ?_, rowCopy⟩
  rw [result]
  simpa only [rowAt, if_neg (by omega : source + (a.length - p) ≠ 0),
    List.getElem?_append_right (by rw [prefixLength]; omega :
      (a.take (a.length - 1)).length ≤ source + (a.length - p) - 1), index] using atBlock

end IBLP
