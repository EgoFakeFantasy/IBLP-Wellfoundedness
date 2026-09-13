import IBLP.Realization.CopyTrace

namespace IBLP

theorem FactorTrace.member_le_start {a : Pattern} {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) : ∀ r ∈ rows, r ≤ start := by
  induction h with
  | single => simp
  | @cons start next rows _ smaller inner ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact le_rfl
    · exact (ih r hr).trans smaller.le

theorem FactorTrace.decreasing {a : Pattern} {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) : rows.Pairwise (· > ·) := by
  induction h with
  | single => simp
  | @cons start next rows _ smaller inner ih =>
    exact List.pairwise_cons.mpr ⟨fun r hr => (inner.member_le_start r hr).trans_lt smaller, ih⟩

theorem decreasing_last_le {xs : List Nat} {bottom r : Nat} (decreasing : xs.Pairwise (· > ·))
    (last : xs.getLast? = some bottom) (member : r ∈ xs) : bottom ≤ r := by
  obtain ⟨i, hi, value⟩ := List.mem_iff_getElem.mp member
  rw [List.getLast?_eq_getElem?] at last
  obtain ⟨hj, endValue⟩ := List.getElem?_eq_some_iff.mp last
  by_cases earlier : i < xs.length - 1
  · have less := List.pairwise_iff_getElem.mp decreasing i (xs.length - 1) hi hj earlier
    simpa only [value, endValue] using less.le
  · have same : i = xs.length - 1 := by omega
    subst i
    exact (endValue.symm.trans value).le

theorem fromRight_two_append {xs : List Nat} (nonempty : xs ≠ []) (target bottom : Nat) :
    fromRight (xs ++ [target]) 2 = some bottom ↔ xs.getLast? = some bottom := by
  have length : 0 < xs.length := List.length_pos_iff.mpr nonempty
  have index : xs.length + 1 - 2 = xs.length - 1 := by omega
  simp only [fromRight, List.length_append, List.length_singleton,
    show 0 < 2 ∧ 2 ≤ xs.length + 1 by omega, and_self, ↓reduceIte, index,
    List.getElem?_append_left (by omega : xs.length - 1 < xs.length), List.getLast?_eq_getElem?]

/-- The literal bottom-factor test in the full-copy filter implies that
every nonterminal factor belongs to the copied tail. -/
theorem FactorTrace.tail_of_bottom {a : Pattern} {target start p bottom : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) (bottomAt : fromRight (rows ++ [target]) 2 = some bottom)
    (inTail : p ≤ bottom) : ∀ r ∈ rows, p ≤ r := by
  have last := (fromRight_two_append h.nonempty target bottom).mp bottomAt
  exact fun r hr => inTail.trans (decreasing_last_le h.decreasing last hr)

end IBLP
