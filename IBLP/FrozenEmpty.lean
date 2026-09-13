import IBLP.FrozenGeometry

namespace IBLP

theorem FrozenReach.of_empty_row {initial current : Pattern} {rec : Records} {owner : Nat}
    {pending : List Nat} (absent : rowAt initial owner = none)
    (reach : FrozenReach initial rec owner current pending) : current = initial ∧ pending = [] := by
  induction reach with
  | start => exact ⟨rfl, by simp [frozenMarks, absent]⟩
  | next previous ih => simp at ih

theorem FrozenGeometryBefore.of_empty_row {initial : Pattern} {rec : Records} {owner remaining : Nat}
    (absent : rowAt initial owner = none) : FrozenGeometryBefore initial rec owner remaining := by
  intro current mark pending reach
  have empty := reach.of_empty_row absent
  simp at empty

end IBLP
