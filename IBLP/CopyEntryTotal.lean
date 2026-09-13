import IBLP.CopyEntry

namespace IBLP

theorem Row.explicit_edge_increases {row : Row} {n : Nat} (valid : row.BasicValid n)
    (shape : row.OrdinaryShape) {edge : Nat × Nat}
    (member : edge ∈ row.columns.zip (row.columns.drop row.step)) : edge.1 < edge.2 := by
  obtain ⟨i, bound, value⟩ := List.mem_iff_getElem.mp member
  have indices : i < row.columns.length ∧ row.step + i < row.columns.length := by
    simp only [List.length_zip, List.length_drop] at bound
    omega
  have pair : (row.columns[i], row.columns[row.step + i]) = edge := by
    simpa only [List.getElem_zip, List.getElem_drop] using value
  have less := List.pairwise_iff_getElem.mp valid.1 i (row.step + i) indices.1 indices.2
    (by have := Row.step_pos shape; omega)
  simpa only [← pair] using less

theorem copyEntry_inflationary {n minimum p x y : Nat} {last : Row}
    (valid : last.BasicValid n) (shape : last.OrdinaryShape)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (copied : copyEntry n last x = some y) : x ≤ y := by
  rcases copyEntry_cases hm hp copied with ⟨_, equal⟩ | ⟨_, _, equal⟩ | ⟨_, _, edge⟩
  · omega
  · omega
  · exact (Row.explicit_edge_increases valid shape edge).le

theorem copyEntry_exists_of_edge {n minimum p x y : Nat} {last : Row}
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (edge : (x, y) ∈ last.columns.zip (last.columns.drop last.step)) :
    ∃ value, copyEntry n last x = some value := by
  by_cases low : x < minimum
  · exact ⟨x, by simp [copyEntry, hm, hp, low]⟩
  · by_cases high : p ≤ x
    · exact ⟨x + (n - p), by simp [copyEntry, hm, hp, low, high]⟩
    · cases found : (last.columns.zip (last.columns.drop last.step)).find? (fun pair => pair.1 == x) with
      | none =>
        have impossible := (List.find?_eq_none.mp found) (x, y) edge
        simp at impossible
      | some pair => exact ⟨pair.2, by simp [copyEntry, hm, hp, low, high, found]⟩

end IBLP
