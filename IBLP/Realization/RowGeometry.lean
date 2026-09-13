import IBLP.Realization.TraceGeometry
import IBLP.Realization.FiniteTraceRows
import IBLP.Rank.RootOwners

namespace IBLP

/-- The source endpoint is read from the finite row, with a default only at
indices that are not used as genuine rows. -/
def rowEndpoint (a : Pattern) (r : Nat) : Nat :=
  ((rowAt a r).bind Row.e).getD 0

theorem rowEndpoint_eq {a : Pattern} {r e : Nat} {row : Row}
    (hr : rowAt a r = some row) (he : row.e = some e) : rowEndpoint a r = e := by
  simp [rowEndpoint, hr, he]

theorem finiteRow_endpoint_exists {a : Pattern} (shapes : OrdinaryShape a)
    (r : FiniteRowIndex a) : ∃ row,
      rowAt a r.val = some row ∧ row.e = some (rowEndpoint a r.val) := by
  obtain ⟨row, hr⟩ := rowAt_exists r.property.1 r.property.2
  have ordinary := shapes row (rowAt_mem hr)
  obtain ⟨e, he⟩ := fromRight_exists (Row.step_pos ordinary) (Row.step_lt_length ordinary).le
  exact ⟨row, hr, (rowEndpoint_eq hr he) ▸ he⟩

theorem Row.column_le_last {r c : Nat} {row : Row} (valid : row.BasicValid r)
    (hc : c ∈ row.columns) : c ≤ r := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hc
  have last := valid.2.2.1
  rw [List.getLast?_eq_getElem?] at last
  obtain ⟨hj, hjval⟩ := List.getElem?_eq_some_iff.mp last
  by_cases hlt : i < row.columns.length - 1
  · have smaller := List.pairwise_iff_getElem.mp valid.1 i
      (row.columns.length - 1) hi hj hlt
    simpa only [he, hjval] using smaller.le
  · have same : i = row.columns.length - 1 := by omega
    subst i
    exact (he.symm.trans hjval).le

theorem Row.edge_index_bounds {r : Nat} {row : Row} (valid : row.BasicValid r)
    {edge : Nat × Nat} (he : edge ∈ row.edgePairs r) : edge.1 ≤ r + 1 ∧ edge.2 ≤ r + 1 := by
  obtain ⟨left, right⟩ := List.of_mem_zip he
  have bound (c : Nat) (hc : c ∈ row.columns ++ [r + 1]) : c ≤ r + 1 := by
    rcases List.mem_append.mp hc with hc | hc
    · exact (Row.column_le_last valid hc).trans (Nat.le_succ _)
    · exact (List.mem_singleton.mp hc).le
  exact ⟨bound _ left, bound _ (List.mem_of_mem_drop right)⟩

theorem Row.properMark_lt {r b : Nat} {row : Row} (valid : row.BasicValid r)
    (proper : row.ProperMark b) : b < r := by
  obtain ⟨i, hi, _, bound⟩ := proper
  obtain ⟨hindex, hvalue⟩ := List.getElem?_eq_some_iff.mp hi
  have last := valid.2.2.1
  rw [List.getLast?_eq_getElem?] at last
  obtain ⟨hlast, lastValue⟩ := List.getElem?_eq_some_iff.mp last
  have smaller := List.pairwise_iff_getElem.mp valid.1 i
    (row.columns.length - 1) hindex hlast (by omega)
  simpa only [hvalue, lastValue] using smaller

private theorem pair_mem_zip_of_getElem? {xs ys : List Nat} {i x y : Nat}
    (hx : xs[i]? = some x) (hy : ys[i]? = some y) : (x, y) ∈ xs.zip ys := by
  obtain ⟨hi, hix⟩ := List.getElem?_eq_some_iff.mp hx
  obtain ⟨hj, hjy⟩ := List.getElem?_eq_some_iff.mp hy
  apply List.mem_iff_getElem.mpr
  refine ⟨i, by simp only [List.length_zip]; omega, ?_⟩
  simp only [List.getElem_zip, hix, hjy]

/-- The p edge is among the literal L-step pairs, for every legal row. -/
theorem Row.predecessor_edge {r p : Nat} {row : Row} (valid : row.BasicValid r)
    (shape : row.OrdinaryShape) (hp : row.p = some p) : (p, r) ∈ row.edgePairs r := by
  have hs := Row.step_pos shape
  have hl := Row.step_lt_length shape
  have source : row.columns[row.columns.length - (row.step + 1)]? = some p := by
    simpa only [Row.p, fromRight, show 0 < row.step + 1 ∧ row.step + 1 ≤ row.columns.length by omega,
      ↓reduceIte] using hp
  apply pair_mem_zip_of_getElem? (i := row.columns.length - (row.step + 1))
  · rw [List.getElem?_append_left (by omega)]
    exact source
  · rw [List.getElem?_drop]
    have eq : row.step + (row.columns.length - (row.step + 1)) = row.columns.length - 1 := by omega
    rw [eq, List.getElem?_append_left (by omega), ← List.getLast?_eq_getElem?]
    exact valid.2.2.1

/-- The final L-step pair has the manuscript's implicit endpoint r+1. -/
theorem Row.endpoint_edge {r e : Nat} {row : Row} (shape : row.OrdinaryShape)
    (he : row.e = some e) : (e, r + 1) ∈ row.edgePairs r := by
  have hs := Row.step_pos shape
  have hl := Row.step_lt_length shape
  have source : row.columns[row.columns.length - row.step]? = some e := by
    simpa only [Row.e, fromRight, show 0 < row.step ∧ row.step ≤ row.columns.length by omega,
      ↓reduceIte] using he
  apply pair_mem_zip_of_getElem? (i := row.columns.length - row.step)
  · rw [List.getElem?_append_left (by omega)]
    exact source
  · rw [List.getElem?_drop]
    have eq : row.step + (row.columns.length - row.step) = row.columns.length := by omega
    rw [eq, List.getElem?_append_right (by omega)]
    simp

end IBLP
