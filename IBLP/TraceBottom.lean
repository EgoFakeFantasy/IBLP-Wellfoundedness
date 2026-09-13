import IBLP.TraceBounds

namespace IBLP

theorem fromRight_two_dropLast (xs : List Nat) : fromRight xs 2 = xs.dropLast.getLast? := by
  rw [List.getLast?_dropLast]
  by_cases small : xs.length ≤ 1
  · simp [fromRight, small, show ¬ 2 ≤ xs.length by omega]
  · simp [fromRight, small, show 2 ≤ xs.length by omega]

theorem getLast_append_of_nonempty {suffix : List Nat} (nonempty : suffix ≠ []) (front : List Nat) :
    (front ++ suffix).getLast? = suffix.getLast? := by
  cases atLast : suffix.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp atLast))
  | some last => simp [List.getLast?_append, atLast]

/-- Changing any initial factors or the paired terminal source leaves the
bottom factor unchanged when the same nonempty suffix is retained. -/
theorem fromRight_two_same_suffix {front next suffix : List Nat} {source target bottom : Nat}
    (nonempty : suffix ≠ []) (old : fromRight ((front ++ suffix) ++ [source]) 2 = some bottom) :
    fromRight ((next ++ suffix) ++ [target]) 2 = some bottom := by
  have oldNonempty : front ++ suffix ≠ [] := by simp [nonempty]
  have newNonempty : next ++ suffix ≠ [] := by simp [nonempty]
  rw [fromRight_two_append oldNonempty, getLast_append_of_nonempty nonempty] at old
  exact (fromRight_two_append newNonempty target bottom).mpr
    ((getLast_append_of_nonempty nonempty next).trans old)

end IBLP
