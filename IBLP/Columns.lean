import IBLP.Operations
import FullMarkedBLP.Columns
import FullMarkedBLP.CopyPredecessor

namespace IBLP

theorem insertColumn_eq_upstream (x : Nat) (xs : List Nat) :
    insertColumn x xs = FullMarkedBLP.insertColumn x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [insertColumn, FullMarkedBLP.insertColumn, ih]

/-- Only the identical pure sorting helper is shared with the fixed upstream
revision; the IBLP copying and expansion programs remain their own functions. -/
theorem canonicalColumns_eq_upstream (xs : List Nat) :
    canonicalColumns xs = FullMarkedBLP.canonicalColumns xs := by
  have same : insertColumn = FullMarkedBLP.insertColumn := by
    funext x ys
    exact insertColumn_eq_upstream x ys
  simp only [canonicalColumns, FullMarkedBLP.canonicalColumns, same]

theorem mem_canonicalColumns (z : Nat) (xs : List Nat) : z ∈ canonicalColumns xs ↔ z ∈ xs := by
  rw [canonicalColumns_eq_upstream]
  exact FullMarkedBLP.mem_canonicalColumns z xs

theorem canonicalColumns_sorted (xs : List Nat) : (canonicalColumns xs).Pairwise (· < ·) := by
  rw [canonicalColumns_eq_upstream]
  exact FullMarkedBLP.canonicalColumns_sorted xs

theorem canonicalColumns_of_sorted {xs : List Nat} (sorted : xs.Pairwise (· < ·)) :
    canonicalColumns xs = xs := by
  rw [canonicalColumns_eq_upstream]
  exact FullMarkedBLP.canonicalColumns_of_sorted sorted

theorem mapped_mem_left {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : FullMarkedBLP.MapsEntries f xs ys) {x : α} (hx : x ∈ xs) :
    ∃ y ∈ ys, f x = some y := by
  obtain ⟨i, hi, value⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨y, hy, mapped⟩ := h.at_left (List.getElem?_eq_some_iff.mpr ⟨hi, value⟩)
  obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp hy
  exact ⟨y, List.mem_iff_getElem.mpr ⟨i, bound, equal⟩, mapped⟩

end IBLP
