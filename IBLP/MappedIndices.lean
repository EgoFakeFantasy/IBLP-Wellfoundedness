import IBLP.MappedColumns
import Mathlib.Data.List.Basic

namespace IBLP

theorem sorted_idxOf_of_at {xs : List Nat} (sorted : xs.Pairwise (· < ·))
    {i x : Nat} (atIndex : xs[i]? = some x) : xs.idxOf x = i := by
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp atIndex
  have nodup : xs.Nodup := List.Pairwise.imp (fun h => Nat.ne_of_lt h) sorted
  simpa only [value] using nodup.idxOf_getElem i bound

theorem mapped_idxOf {f : Nat → Option Nat} {xs ys : List Nat}
    (mapped : FullMarkedBLP.MapsEntries f xs ys) (sorted : ys.Pairwise (· < ·))
    {x y : Nat} (member : x ∈ xs) (image : f x = some y) : ys.idxOf y = xs.idxOf x := by
  obtain ⟨value, atIndex, mappedValue⟩ := mapped.at_left (List.getElem?_idxOf member)
  have same := Option.some.inj (mappedValue.symm.trans image)
  exact sorted_idxOf_of_at sorted (atIndex.trans (congrArg some same))

theorem Row.properMark_indices {row : Row} {owner x : Nat} (valid : row.BasicValid owner)
    (proper : row.ProperMark x) : x ∈ row.columns ∧ row.step + 1 ≤ row.columns.idxOf x ∧
      row.columns.idxOf x + 1 < row.columns.length := by
  obtain ⟨i, atIndex, above, below⟩ := proper
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp atIndex
  have index := sorted_idxOf_of_at valid.1 atIndex
  exact ⟨List.mem_iff_getElem.mpr ⟨i, bound, value⟩, by omega, by omega⟩

end IBLP
