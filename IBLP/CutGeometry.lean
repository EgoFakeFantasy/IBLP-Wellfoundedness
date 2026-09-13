import IBLP.PrefixGeometry

namespace IBLP

theorem cut_decomposition {a b : Pattern} (run : cut a = some b) :
    0 < a.length ∧ b = a.take (a.length - 1) := by
  have positive : 0 < a.length := by
    cases a with
    | nil => simp [cut] at run
    | cons row rest => exact Nat.zero_lt_succ _
  refine ⟨positive, ?_⟩
  unfold cut at run
  split at run
  · simp at run
  · exact (Option.some.inj run).symm.trans List.dropLast_eq_take

theorem cut_defined {a : Pattern} (nonempty : 0 < a.length) :
    cut a = some (a.take (a.length - 1)) := by
  have hn : a.isEmpty = false := by cases a <;> simp_all
  simp [cut, hn, List.dropLast_eq_take]

theorem cut_length {a b : Pattern} (run : cut a = some b) : b.length = a.length - 1 := by
  rw [(cut_decomposition run).2, List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]

end IBLP
