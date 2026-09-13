import IBLP.Operations
import IBLP.Realization.RowGeometry

namespace IBLP

theorem Row.minimum_le_column {row : Row} {n minimum x : Nat} (valid : row.BasicValid n)
    (hm : row.columns.head? = some minimum) (member : x ∈ row.columns) : minimum ≤ x := by
  obtain ⟨i, hi, value⟩ := List.mem_iff_getElem.mp member
  obtain ⟨hz, head⟩ := List.getElem?_eq_some_iff.mp
    (show row.columns[0]? = some minimum by simpa only [List.head?_eq_getElem?] using hm)
  by_cases zero : i = 0
  · subst i
    exact (head.symm.trans value).le
  · have less := List.pairwise_iff_getElem.mp valid.1 0 i hz hi (by omega)
    simpa only [head, value] using less.le

theorem fromRight_mem {xs : List Nat} {k x : Nat} (h : fromRight xs k = some x) : x ∈ xs := by
  unfold fromRight at h
  split at h
  · obtain ⟨hi, value⟩ := List.getElem?_eq_some_iff.mp h
    exact List.mem_iff_getElem.mpr ⟨_, hi, value⟩
  · simp at h

theorem copyEntry_tail {last : Row} {n minimum p x : Nat}
    (valid : last.BasicValid n) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (tail : p ≤ x) : copyEntry n last x = some (x + (n - p)) := by
  have first := Row.minimum_le_column valid hm (fromRight_mem hp)
  simp [copyEntry, hm, hp, show ¬x < minimum by omega, tail]

theorem Row.explicit_edge {row : Row} {n : Nat} {edge : Nat × Nat}
    (member : edge ∈ row.columns.zip (row.columns.drop row.step)) : edge ∈ row.edgePairs n := by
  obtain ⟨i, hi, value⟩ := List.mem_iff_getElem.mp member
  have hib : i < min row.columns.length (row.columns.drop row.step).length := by
    simpa only [List.length_zip] using hi
  have left : i < row.columns.length := lt_of_lt_of_le hib (Nat.min_le_left _ _)
  have right : i < (row.columns.drop row.step).length :=
    lt_of_lt_of_le hib (Nat.min_le_right _ _)
  have shifted : row.step + i < row.columns.length := by
    simp only [List.length_drop] at right
    omega
  apply List.mem_iff_getElem.mpr
  refine ⟨i, ?_, ?_⟩
  · simp only [Row.edgePairs, List.length_zip, List.length_append, List.length_singleton,
      List.length_drop]
    omega
  · simpa only [Row.edgePairs, List.getElem_zip, List.getElem_drop,
      List.getElem_append_left left, List.getElem_append_left shifted] using value

/-- Exact branches of the original partial point map, including the full
unbounded translated tail rather than an older bounded-tail convention. -/
theorem copyEntry_cases {n minimum p x y : Nat} {last : Row}
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (copied : copyEntry n last x = some y) :
    (x < minimum ∧ y = x) ∨
      (minimum ≤ x ∧ p ≤ x ∧ y = x + (n - p)) ∨
      (minimum ≤ x ∧ x < p ∧ (x, y) ∈ last.columns.zip (last.columns.drop last.step)) := by
  simp only [copyEntry, hm, hp] at copied
  change (if x < minimum then some x else if p ≤ x then some (x + (n - p)) else
    ((last.columns.zip (last.columns.drop last.step)).find? (fun pair => pair.1 == x)).bind
      (fun pair => some pair.2)) = some y at copied
  split at copied
  · exact Or.inl ⟨by assumption, (Option.some.inj copied).symm⟩
  · rename_i above
    split at copied
    · exact Or.inr (Or.inl ⟨by omega, by assumption, (Option.some.inj copied).symm⟩)
    · rename_i below
      obtain ⟨pair, found, result⟩ := Option.bind_eq_some_iff.mp copied
      have fst : pair.1 = x := by simpa only [beq_iff_eq] using List.find?_some found
      have snd : pair.2 = y := Option.some.inj result
      exact Or.inr (Or.inr ⟨by omega, by omega,
        by simpa only [← fst, ← snd] using List.mem_of_find?_eq_some found⟩)

theorem copyEntry_bound {n minimum p x y : Nat} {last : Row}
    (valid : last.BasicValid n) (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (bound : x ≤ n + 1) (copied : copyEntry n last x = some y) : y ≤ n + (n - p) + 1 := by
  rcases copyEntry_cases hm hp copied with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, edge⟩
  · omega
  · omega
  · have yn := Row.column_le_last valid (List.mem_of_mem_drop (List.of_mem_zip edge).2)
    omega

end IBLP
