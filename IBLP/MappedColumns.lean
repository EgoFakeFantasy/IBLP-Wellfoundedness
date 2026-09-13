import IBLP.Columns

namespace IBLP
open FullMarkedBLP

theorem mapped_append {α β : Type} {f : α → Option β} {xs xs' : List α} {ys ys' : List β}
    (left : MapsEntries f xs ys) (right : MapsEntries f xs' ys') :
    MapsEntries f (xs ++ xs') (ys ++ ys') := by
  induction left with
  | nil => exact right
  | cons head _ ih => exact MapsEntries.cons head ih

theorem mapped_fromRight {f : Nat → Option Nat} {xs ys : List Nat}
    (mapped : MapsEntries f xs ys) {k y : Nat} (hy : IBLP.fromRight ys k = some y) :
    ∃ x, IBLP.fromRight xs k = some x ∧ f x = some y := by
  unfold IBLP.fromRight at hy
  split at hy
  · rename_i bounds
    obtain ⟨x, hx, image⟩ := mapped.at hy
    refine ⟨x, ?_, image⟩
    simpa only [IBLP.fromRight, mapped.length_eq, bounds, ↓reduceIte] using hx
  · simp at hy

/-- Every step pair in a mapped list comes from the pair at the same two
source indices; the statement also applies to appended implicit endpoints. -/
theorem mapped_zip_drop {f : Nat → Option Nat} {xs ys : List Nat}
    (mapped : MapsEntries f xs ys) (step : Nat) {edge : Nat × Nat}
    (member : edge ∈ ys.zip (ys.drop step)) :
    ∃ old ∈ xs.zip (xs.drop step), f old.1 = some edge.1 ∧ f old.2 = some edge.2 := by
  obtain ⟨i, bound, value⟩ := List.mem_iff_getElem.mp member
  have pairAt : (ys.zip (ys.drop step))[i]? = some edge :=
    List.getElem?_eq_some_iff.mpr ⟨bound, value⟩
  rw [List.getElem?_zip_eq_some, List.getElem?_drop] at pairAt
  obtain ⟨x, hx, fx⟩ := mapped.at pairAt.1
  obtain ⟨y, hy, fy⟩ := mapped.at pairAt.2
  have oldAt : (xs.zip (xs.drop step))[i]? = some (x, y) := by
    rw [List.getElem?_zip_eq_some, List.getElem?_drop]
    exact ⟨hx, hy⟩
  obtain ⟨oldBound, oldValue⟩ := List.getElem?_eq_some_iff.mp oldAt
  exact ⟨(x, y), List.mem_iff_getElem.mpr ⟨i, oldBound, oldValue⟩, fx, fy⟩

theorem mapped_fromRight_left {f : Nat → Option Nat} {xs ys : List Nat}
    (mapped : MapsEntries f xs ys) {k x : Nat} (hx : IBLP.fromRight xs k = some x) :
    ∃ y, IBLP.fromRight ys k = some y ∧ f x = some y := by
  unfold IBLP.fromRight at hx
  split at hx
  · rename_i bounds
    obtain ⟨y, hy, image⟩ := mapped.at_left hx
    refine ⟨y, ?_, image⟩
    simpa only [IBLP.fromRight, ← mapped.length_eq, bounds, ↓reduceIte] using hy
  · simp at hx

theorem mapped_zip_drop_left {f : Nat → Option Nat} {xs ys : List Nat}
    (mapped : MapsEntries f xs ys) (step : Nat) {edge : Nat × Nat}
    (member : edge ∈ xs.zip (xs.drop step)) :
    ∃ target ∈ ys.zip (ys.drop step), f edge.1 = some target.1 ∧ f edge.2 = some target.2 := by
  obtain ⟨i, bound, value⟩ := List.mem_iff_getElem.mp member
  have pairAt : (xs.zip (xs.drop step))[i]? = some edge :=
    List.getElem?_eq_some_iff.mpr ⟨bound, value⟩
  rw [List.getElem?_zip_eq_some, List.getElem?_drop] at pairAt
  obtain ⟨x, hx, fx⟩ := mapped.at_left pairAt.1
  obtain ⟨y, hy, fy⟩ := mapped.at_left pairAt.2
  have newAt : (ys.zip (ys.drop step))[i]? = some (x, y) := by
    rw [List.getElem?_zip_eq_some, List.getElem?_drop]
    exact ⟨hx, hy⟩
  obtain ⟨newBound, newValue⟩ := List.getElem?_eq_some_iff.mp newAt
  exact ⟨(x, y), List.mem_iff_getElem.mpr ⟨i, newBound, newValue⟩, fx, fy⟩

end IBLP
