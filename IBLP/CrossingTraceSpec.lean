import IBLP.TracePieces

namespace IBLP

theorem find_below_exists {xs : List Nat} {p bottom : Nat} (member : bottom ∈ xs) (below : bottom < p) :
    ∃ boundary, xs.find? (· < p) = some boundary := by
  induction xs with
  | nil => simp at member
  | cons r rs ih =>
    by_cases low : r < p
    · exact ⟨r, by simp [List.find?, low]⟩
    · have rest : bottom ∈ rs := by rcases List.mem_cons.mp member with same | rest; omega; exact rest
      obtain ⟨boundary, found⟩ := ih rest
      exact ⟨boundary, by simpa [List.find?, low] using found⟩

/-- For a crossing mark, the first point below p is a nonterminal factor.
The filter searches the complete trace, including its paired source. -/
theorem FactorTrace.first_below_factors {a : Pattern} {target start p bottom boundary : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows)
    (bottomAt : fromRight (rows ++ [target]) 2 = some bottom) (crossing : bottom < p)
    (found : (rows ++ [target]).find? (· < p) = some boundary) :
    rows.find? (· < p) = some boundary := by
  have last := (fromRight_two_append h.nonempty target bottom).mp bottomAt
  rw [List.getLast?_eq_getElem?] at last
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp last
  have member := List.mem_iff_getElem.mpr ⟨_, bound, value⟩
  obtain ⟨first, firstAt⟩ := find_below_exists member crossing
  have same : first = boundary := by simpa [List.find?_append, firstAt] using found
  exact firstAt.trans (congrArg some same)

end IBLP
