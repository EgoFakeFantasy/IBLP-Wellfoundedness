import IBLP.TraceBounds

namespace IBLP

/-- A possibly empty initial segment of an accurate predecessor chain.
Its list excludes the terminal boundary, which belongs to the suffix. -/
inductive FactorPrefix (a : Pattern) (target : Nat) : Nat → List Nat → Prop
  | nil : FactorPrefix a target target []
  | cons {start next : Nat} {rows : List Nat} : predecessor a start = some next → next < start →
      FactorPrefix a target next rows → FactorPrefix a target start (start :: rows)

theorem FactorPrefix.appendTrace {a : Pattern} {boundary start target : Nat} {front rows : List Nat}
    (h : FactorPrefix a boundary start front) (suffix : FactorTrace a target boundary rows) :
    FactorTrace a target start (front ++ rows) := by
  induction h with
  | nil => exact suffix
  | cons hp hn inner ih => exact .cons hp hn ih

theorem FactorTrace.toPrefix {a : Pattern} {target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) : FactorPrefix a target start rows := by
  induction h with
  | single hp hn => exact .cons hp hn .nil
  | cons hp hn inner ih => exact .cons hp hn ih

theorem FactorTrace.append {a : Pattern} {boundary start target : Nat} {front rows : List Nat}
    (h : FactorTrace a boundary start front) (suffix : FactorTrace a target boundary rows) :
    FactorTrace a target start (front ++ rows) := h.toPrefix.appendTrace suffix

/-- The first factor below the copying threshold gives a literal front
and suffix decomposition. Every front factor is in the copied tail. -/
theorem FactorTrace.split_first_below {a : Pattern} {target start p boundary : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) (found : rows.find? (· < p) = some boundary) :
    ∃ front suffix, rows = front ++ suffix ∧ FactorPrefix a boundary start front ∧
      FactorTrace a target boundary suffix ∧ (∀ r ∈ front, p ≤ r) ∧ boundary < p := by
  induction h with
  | @single r hp hn =>
    by_cases low : r < p
    · have same : r = boundary := by simpa [List.find?, low] using found
      subst boundary
      exact ⟨[], [r], rfl, .nil, .single hp hn, by simp, low⟩
    · simp [List.find?, low] at found
  | @cons r next rows hp hn inner ih =>
    by_cases low : r < p
    · have same : r = boundary := by simpa [List.find?, low] using found
      subst boundary
      exact ⟨[], r :: rows, rfl, .nil, .cons hp hn inner, by simp, low⟩
    · have found' : rows.find? (· < p) = some boundary := by simpa [List.find?, low] using found
      obtain ⟨front, suffix, split, before, after, tail, below⟩ := ih found'
      refine ⟨r :: front, suffix, by simp only [List.cons_append, split], .cons hp hn before, after, ?_, below⟩
      intro t ht
      rcases List.mem_cons.mp ht with same | member
      · omega
      · exact tail t member

end IBLP
