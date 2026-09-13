import IBLP.Columns

namespace IBLP

/-- The successful output consists of the retained n-1 rows followed by
the entire source interval p,...,n, including the copied control row. -/
theorem rawCopy_decomposition {a b : Pattern} (copy : rawCopy a = some b) :
    ∃ last p block, a.getLast? = some last ∧ last.p = some p ∧ 0 < p ∧ p ≤ a.length ∧
      ((List.range (a.length - p + 1)).map (p + ·)).mapM (copyRow a last) = some block ∧
      b = a.take (a.length - 1) ++ block := by
  obtain ⟨last, hlast, copy⟩ := Option.bind_eq_some_iff.mp copy
  obtain ⟨p, hp, copy⟩ := Option.bind_eq_some_iff.mp copy
  obtain ⟨block, hblock, result⟩ := Option.bind_eq_some_iff.mp copy
  have first : ((List.range (a.length - p + 1)).map (p + ·))[0]? = some p := by simp
  obtain ⟨copied, _, rowCopy⟩ := (FullMarkedBLP.option_mapM_forall2 hblock).at_left first
  obtain ⟨row, rowExists, _⟩ := Option.bind_eq_some_iff.mp rowCopy
  exact ⟨last, p, block, hlast, hp, rowAt_pos rowExists, rowAt_le_length rowExists,
    hblock, (Option.some.inj result).symm⟩

theorem getLast_rowAt {a : Pattern} {last : Row} (h : a.getLast? = some last) :
    rowAt a a.length = some last := by
  have hn : 0 < a.length := by
    cases a with
    | nil => simp at h
    | cons row rows => simp
  simpa only [rowAt, if_neg (Nat.ne_of_gt hn), List.getLast?_eq_getElem?] using h

theorem rawCopy_length {a b : Pattern} {last : Row} {p : Nat}
    (copy : rawCopy a = some b) (hlast : a.getLast? = some last) (hp : last.p = some p) :
    b.length = a.length + (a.length - p) := by
  obtain ⟨last', p', block, hlast', hp', positive, included, hblock, result⟩ := rawCopy_decomposition copy
  have sameLast : last' = last := Option.some.inj (hlast'.symm.trans hlast)
  subst last'
  have sameP : p' = p := Option.some.inj (hp'.symm.trans hp)
  subst p'
  have length := FullMarkedBLP.option_mapM_length hblock
  simp only [List.length_map, List.length_range] at length
  rw [result, List.length_append, List.length_take, length]
  omega

theorem rawCopy_prefix {a b : Pattern} {r : Nat} (copy : rawCopy a = some b) (old : r < a.length) :
    rowAt b r = rowAt a r := by
  obtain ⟨last, p, block, _, _, positive, included, _, result⟩ := rawCopy_decomposition copy
  by_cases zero : r = 0
  · simp [zero, rowAt]
  · rw [result]
    simp only [rowAt, if_neg zero, List.getElem?_append_left
      (by simp only [List.length_take]; omega : r - 1 < (a.take (a.length - 1)).length)]
    rw [List.getElem?_take_of_lt (by omega)]

theorem rawCopy_row_origin {a b : Pattern} {last copied : Row} {p target : Nat}
    (copy : rawCopy a = some b) (hlast : a.getLast? = some last) (hp : last.p = some p)
    (afterPrefix : a.length ≤ target) (ht : rowAt b target = some copied) :
    ∃ source, p ≤ source ∧ source ≤ a.length ∧ target = source + (a.length - p) ∧
      copyRow a last source = some copied := by
  obtain ⟨last', p', block, hlast', hp', positive, included, hblock, result⟩ := rawCopy_decomposition copy
  have sameLast : last' = last := Option.some.inj (hlast'.symm.trans hlast)
  subst last'
  have sameP : p' = p := Option.some.inj (hp'.symm.trans hp)
  subst p'
  have prefixLength : (a.take (a.length - 1)).length = a.length - 1 := by simp
  have index : target - 1 - (a.take (a.length - 1)).length = target - a.length := by
    rw [prefixLength]
    omega
  have atBlock : block[target - a.length]? = some copied := by
    rw [result] at ht
    simpa only [rowAt, if_neg (by omega : target ≠ 0), List.getElem?_append_right
      (by rw [prefixLength]; omega : (a.take (a.length - 1)).length ≤ target - 1), index] using ht
  obtain ⟨source, sourceAt, rowCopy⟩ := (FullMarkedBLP.option_mapM_forall2 hblock).at atBlock
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp sourceAt
  have bound' : target - a.length < a.length - p + 1 := by simpa using bound
  have value' : p + (target - a.length) = source := by simpa using value
  exact ⟨source, by omega, by omega, by omega, rowCopy⟩

end IBLP
