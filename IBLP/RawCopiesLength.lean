import IBLP.RawCopy

namespace IBLP

theorem rawCopy_length_le {a b : Pattern} (run : rawCopy a = some b) : a.length ≤ b.length := by
  obtain ⟨last, p, _, hlast, hp, _⟩ := rawCopy_decomposition run
  rw [rawCopy_length run hlast hp]
  omega

theorem rawCopies_length_le {a b : Pattern} {m : Nat} (run : rawCopies m a = some b) :
    a.length ≤ b.length := by
  induction m generalizing a b with
  | zero => exact (congrArg List.length (Option.some.inj run)).le
  | succ m ih =>
    obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp run
    exact (rawCopy_length_le first).trans (ih rest)

end IBLP
