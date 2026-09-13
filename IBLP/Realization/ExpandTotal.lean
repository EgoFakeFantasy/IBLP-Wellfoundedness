import IBLP.Realization.ExpandRealized

namespace IBLP.BoundedRealization
universe u

/-- Every parameter of the exact original expansion is defined on a
nonempty completely realized pattern. Only the original failed-first-copy
fallback is used; all later copies and the frozen scan are proved total. -/
theorem expand_total {stage : ModelStage.{u}} {a : Pattern} (R : BoundedRealization stage a)
    (nonempty : 0 < a.length) (m : Nat) : ∃ b, expand a m = some b := by
  have notEmpty : a.isEmpty = false := by cases a <;> simp_all
  have fallback := cut_defined nonempty
  by_cases simple : m = 0 ∨ isSuccessor a
  · exact ⟨_, by simpa only [expand, notEmpty, Bool.false_eq_true, if_false, if_pos simple] using fallback⟩
  · cases firstRun : rawCopy a with
    | none =>
      exact ⟨_, by simpa only [expand, notEmpty, Bool.false_eq_true, if_false, if_neg simple, firstRun] using fallback⟩
    | some first =>
      obtain ⟨copied, initial, copies, cut, next, j, entry, _, _, _⟩ :=
        R.toMarkedRealization.copies_cut_realization_exists ⟨first, firstRun⟩ m
      obtain ⟨last, p, _, atLast, hp, _, _, _⟩ := rawCopy_decomposition firstRun
      obtain ⟨result, scan, _⟩ := R.copies_scan_total_realized entry atLast hp copies cut
      have nonzero : m ≠ 0 := fun zero => simple (Or.inl zero)
      have count : m = (m - 1) + 1 := by omega
      have rest : rawCopies (m - 1) first = some copied := by
        conv at copies => lhs; arg 1; rw [count]
        simpa only [rawCopies, firstRun, Option.bind_some] using copies
      exact ⟨result, by simp only [expand, notEmpty, Bool.false_eq_true, if_false, if_neg simple,
        firstRun, rest, cut, scan, Bind.bind, Option.bind]⟩

end IBLP.BoundedRealization
