import IBLP.ScanLabels

namespace IBLP

/-- Renumbering one old-label interval either transports an existing row,
or creates a point in precisely the expanded old base's family. -/
theorem label_interval_native {names : Nat → Nat} {cursor width i j : Nat}
    (increasing : StrictMono names) (consecutive : names (cursor + 1) = names cursor + 1)
    (lower : (shiftAfter (names cursor) width ∘ names) i ≤ j)
    (upper : j < (shiftAfter (names cursor) width ∘ names) (i + 1)) :
    (∃ old, names i ≤ old ∧ old < names (i + 1) ∧ j = shiftAfter (names cursor) width old) ∨
      (i = cursor ∧ names cursor ≤ j ∧ j ≤ names cursor + width) := by
  simp only [Function.comp_apply] at lower upper
  rcases lt_trichotomy i cursor with before | same | after
  · have first := increasing before
    have last := increasing.monotone (show i + 1 ≤ cursor by omega)
    simp only [shiftAfter, if_neg (by omega : ¬ names cursor < names i)] at lower
    simp only [shiftAfter, if_neg (by omega : ¬ names cursor < names (i + 1))] at upper
    exact Or.inl ⟨j, lower, upper, by simp [shiftAfter, show ¬ names cursor < j by omega]⟩
  · subst i
    simp only [shiftAfter, Nat.lt_irrefl, if_false] at lower
    rw [consecutive] at upper
    simp only [shiftAfter, if_pos (Nat.lt_succ_self _)] at upper
    exact Or.inr ⟨rfl, lower, by omega⟩
  · have first := increasing after
    have last := increasing (show cursor < i + 1 by omega)
    simp only [shiftAfter, if_pos first] at lower
    simp only [shiftAfter, if_pos last] at upper
    exact Or.inl ⟨j - width, by omega, by omega,
      by simp only [shiftAfter, if_pos (show names cursor < j - width by omega)]; omega⟩

end IBLP
