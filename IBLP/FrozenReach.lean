import IBLP.ScanTermination
import IBLP.CompletionTrace

namespace IBLP

/-- The original queue, frozen once at row entrance. Filtering and
canonical sorting are exactly those in completeFrozenMarks. -/
def frozenMarks (a : Pattern) (owner : Nat) : List Nat :=
  match rowAt a owner with
  | none => []
  | some row => canonicalColumns (row.marks.filter (· ∈ row.columns))

theorem completeFrozenMarks_eq_fold (a : Pattern) (rec : Records) (owner : Nat) :
    completeFrozenMarks a rec owner =
      (frozenMarks a owner).foldl (fun cur mark => completeMark cur rec owner mark) a := by
  cases h : rowAt a owner <;> simp [completeFrozenMarks, frozenMarks, h]

/-- Reachable prefixes of that one frozen queue. Newly created marks do
not enter the pending list, and every event uses the same saved records. -/
inductive FrozenReach (initial : Pattern) (rec : Records) (owner : Nat) :
    Pattern → List Nat → Prop
  | start : FrozenReach initial rec owner initial (frozenMarks initial owner)
  | next {current mark pending} : FrozenReach initial rec owner current (mark :: pending) →
      FrozenReach initial rec owner (completeMark current rec owner mark) pending

theorem FrozenReach.advance {initial current : Pattern} {rec : Records} {owner : Nat}
    {todo pending : List Nat} (reach : FrozenReach initial rec owner current (todo ++ pending)) :
    FrozenReach initial rec owner
      (todo.foldl (fun cur mark => completeMark cur rec owner mark) current) pending := by
  induction todo generalizing current with
  | nil => simpa only [List.foldl_nil, List.nil_append] using reach
  | cons mark todo ih =>
    simp only [List.cons_append] at reach
    exact ih (.next reach)

theorem FrozenReach.finish (initial : Pattern) (rec : Records) (owner : Nat) :
    FrozenReach initial rec owner (completeFrozenMarks initial rec owner) [] := by
  rw [completeFrozenMarks_eq_fold]
  exact FrozenReach.advance (by simpa only [List.append_nil] using
    (FrozenReach.start : FrozenReach initial rec owner initial (frozenMarks initial owner)))

theorem FrozenReach.decomposition {initial current : Pattern} {rec : Records} {owner : Nat}
    {pending : List Nat} (reach : FrozenReach initial rec owner current pending) :
    ∃ processed, frozenMarks initial owner = processed ++ pending ∧
      current = processed.foldl (fun cur mark => completeMark cur rec owner mark) initial := by
  induction reach with
  | start => exact ⟨[], rfl, rfl⟩
  | @next current mark pending previous ih =>
    obtain ⟨processed, queue, computed⟩ := ih
    refine ⟨processed ++ [mark], ?_, ?_⟩
    · simpa only [List.append_assoc, List.singleton_append] using queue
    · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, ← computed]

theorem FrozenReach.length {initial current : Pattern} {rec : Records} {owner : Nat}
    {pending : List Nat} (reach : FrozenReach initial rec owner current pending) :
    current.length = initial.length := by
  induction reach with
  | start => rfl
  | next previous ih => rw [completeMark_length, ih]

theorem completeMark_rowAt_other {a : Pattern} {rec : Records} {owner mark i : Nat}
    (other : i ≠ owner) : rowAt (completeMark a rec owner mark) i = rowAt a i := by
  unfold completeMark
  split
  · rename_i row sources atRow guard
    exact rowAt_set_other atRow other
  · rfl

theorem FrozenReach.rowAt_other {initial current : Pattern} {rec : Records} {owner i : Nat}
    {pending : List Nat} (reach : FrozenReach initial rec owner current pending) (other : i ≠ owner) :
    rowAt current i = rowAt initial i := by
  induction reach with
  | start => rfl
  | next previous ih => exact (completeMark_rowAt_other other).trans ih

end IBLP
