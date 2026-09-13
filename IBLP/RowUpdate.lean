import IBLP.CompletionStrongClosure

/-! Single-row update facts for the literal completion program. The list
access proofs follow the pinned FullMarkedBLP CompletionTrace (Apache-2.0). -/
namespace IBLP

theorem rowAt_set_self {a : Pattern} {r : Nat} {old new : Row}
    (hr : rowAt a r = some old) : rowAt (a.set (r - 1) new) r = some new := by
  have hb : 0 < r ∧ r ≤ a.length := ⟨rowAt_pos hr, rowAt_le_length hr⟩
  simp [rowAt, show r ≠ 0 by omega, show r - 1 < a.length by omega]

theorem rowAt_set_other {a : Pattern} {r i : Nat} {old new : Row}
    (hr : rowAt a r = some old) (hi : i ≠ r) :
    rowAt (a.set (r - 1) new) i = rowAt a i := by
  have hb : 0 < r ∧ r ≤ a.length := ⟨rowAt_pos hr, rowAt_le_length hr⟩
  by_cases hz : i = 0
  · subst i; simp [rowAt]
  · simp [rowAt, hz, List.getElem?_set_ne (show r - 1 ≠ i - 1 by omega)]

theorem BasicValid.set {a : Pattern} (valid : BasicValid a) {r : Nat} {old new : Row}
    (hr : rowAt a r = some old) (hnew : new.BasicValid r) : BasicValid (a.set (r - 1) new) := by
  intro i out hi
  by_cases same : i = r
  · subst i
    rw [rowAt_set_self hr] at hi
    cases Option.some.inj hi
    exact hnew
  · rw [rowAt_set_other hr same] at hi
    exact valid i out hi

theorem OrdinaryShape.set {a : Pattern} (shapes : OrdinaryShape a) {r : Nat} {old new : Row}
    (hr : rowAt a r = some old) (hnew : new.OrdinaryShape) : OrdinaryShape (a.set (r - 1) new) := by
  intro out member
  obtain ⟨i, atI⟩ := List.mem_iff_getElem?.mp member
  have atRow : rowAt (a.set (r - 1) new) (i + 1) = some out := by simpa [rowAt] using atI
  by_cases same : i + 1 = r
  · rw [same, rowAt_set_self hr] at atRow
    cases Option.some.inj atRow
    exact hnew
  · rw [rowAt_set_other hr same] at atRow
    exact shapes out (rowAt_mem atRow)

theorem ProperMarks.set {a : Pattern} (proper : ProperMarks a) {r : Nat} {old new : Row}
    (hr : rowAt a r = some old) (hnew : ∀ z ∈ new.marks, new.ProperMark z) :
    ProperMarks (a.set (r - 1) new) := by
  intro out member
  obtain ⟨i, atI⟩ := List.mem_iff_getElem?.mp member
  have atRow : rowAt (a.set (r - 1) new) (i + 1) = some out := by simpa [rowAt] using atI
  by_cases same : i + 1 = r
  · rw [same, rowAt_set_self hr] at atRow
    cases Option.some.inj atRow
    exact hnew
  · rw [rowAt_set_other hr same] at atRow
    exact proper out (rowAt_mem atRow)

theorem predecessor_set_eq {a : Pattern} {r : Nat} {old new : Row}
    (hr : rowAt a r = some old) (hp : new.p = old.p) :
    ∀ i, predecessor (a.set (r - 1) new) i = predecessor a i := by
  intro i
  by_cases same : i = r
  · subst i
    simp only [predecessor, rowAt_set_self hr, hr, Option.bind_some, hp]
  · simp only [predecessor, rowAt_set_other hr same]

theorem Row.CompletionGeometry.set_syntax {a : Pattern} (valid : IBLP.BasicValid a)
    (shapes : IBLP.OrdinaryShape a) (proper : ProperMarks a) {r mark : Nat} {row : Row}
    {sources : List Nat} (hr : rowAt a r = some row)
    (C : row.CompletionGeometry r mark sources) :
    IBLP.BasicValid (a.set (r - 1) (completeMarkRow row mark sources)) ∧
      IBLP.OrdinaryShape (a.set (r - 1) (completeMarkRow row mark sources)) ∧
      ProperMarks (a.set (r - 1) (completeMarkRow row mark sources)) :=
  ⟨valid.set hr (C.basic_valid (valid _ _ hr) (shapes row (rowAt_mem hr)) (proper row (rowAt_mem hr))),
    shapes.set hr (C.shape (valid _ _ hr).1 (shapes row (rowAt_mem hr))),
    proper.set hr (C.all_proper (valid _ _ hr) (shapes row (rowAt_mem hr)) (proper row (rowAt_mem hr)))⟩

end IBLP
