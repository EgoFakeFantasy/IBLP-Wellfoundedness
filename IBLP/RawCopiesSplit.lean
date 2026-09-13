import IBLP.RawCopiesLength

namespace IBLP

theorem rawCopies_add (m n : Nat) (a : Pattern) :
    rawCopies (m + n) a = (rawCopies m a).bind (rawCopies n) := by
  induction m generalizing a with
  | zero => simp only [Nat.zero_add, rawCopies, Option.bind_some]
  | succ m ih =>
    simp only [Nat.succ_add, rawCopies]
    cases first : rawCopy a with
    | none => rfl
    | some middle => exact ih middle

/-- Split an actual successful iteration at any specified copy number. -/
theorem rawCopies_split {a b : Pattern} {m h : Nat}
    (run : rawCopies m a = some b) (within : h ≤ m) :
    ∃ middle, rawCopies h a = some middle ∧ rawCopies (m - h) middle = some b := by
  have split := rawCopies_add h (m - h) a
  rw [Nat.add_sub_of_le within] at split
  rw [split] at run
  exact Option.bind_eq_some_iff.mp run

end IBLP
