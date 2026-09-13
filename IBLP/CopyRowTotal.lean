import IBLP.Columns
import IBLP.Pointers

namespace IBLP

theorem option_mapM_exists {α β : Type} {f : α → Option β} {xs : List α}
    (total : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := total x (List.mem_cons_self)
    obtain ⟨ys, hys⟩ := ih (fun z hz => total z (List.mem_cons_of_mem x hz))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- Totality on the actual columns also covers the exact filtered marks,
because the program explicitly retains only marks in the source columns. -/
theorem copyRow_exists_of_entries {a : Pattern} {last row : Row} {r : Nat}
    (hr : rowAt a r = some row)
    (total : ∀ x ∈ row.columns, ∃ y, copyEntry a.length last x = some y) :
    ∃ copied, copyRow a last r = some copied := by
  obtain ⟨cols, hcols⟩ := option_mapM_exists total
  have marked : ∀ x ∈ row.marks.filter (fun y => y ∈ row.columns &&
      keepCopiedMark a last r row (canonicalColumns cols) y), ∃ y, copyEntry a.length last x = some y := by
    intro x hx
    have condition : x ∈ row.columns ∧ keepCopiedMark a last r row (canonicalColumns cols) x = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using (List.mem_filter.mp hx).2
    exact total x condition.1
  obtain ⟨marks, hmarks⟩ := option_mapM_exists marked
  exact ⟨⟨canonicalColumns cols, row.step, canonicalColumns marks⟩,
    by simp [copyRow, hr, hcols, hmarks]⟩

theorem rawCopy_exists_of_entries {a : Pattern} {last : Row} {p : Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p) (positive : 0 < p) (included : p ≤ a.length)
    (total : ∀ r row, p ≤ r → r ≤ a.length → rowAt a r = some row →
      ∀ x ∈ row.columns, ∃ y, copyEntry a.length last x = some y) :
    ∃ b, rawCopy a = some b := by
  have rows : ∀ r ∈ (List.range (a.length - p + 1)).map (p + ·), ∃ row, copyRow a last r = some row := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have bound := List.mem_range.mp hi
    obtain ⟨row, atRow⟩ := rowAt_exists (by omega : 0 < p + i) (by omega : p + i ≤ a.length)
    exact copyRow_exists_of_entries atRow (total (p + i) row (by omega) (by omega) atRow)
  obtain ⟨block, hblock⟩ := option_mapM_exists rows
  simp only [List.mapM_map] at hblock
  exact ⟨a.take (a.length - 1) ++ block, by simp [rawCopy, hlast, hp, hblock]⟩

end IBLP
