import IBLP.TraceBounds

namespace IBLP

/-- The last vertex of the entrance p chain still above the block's lower
boundary. The descending guard makes the auxiliary definition total even
on malformed patterns; on valid rows it is exactly manuscript section 6.2. -/
def blockSeed (a : Pattern) (lower r : Nat) : Nat :=
  match predecessor a r with
  | none => r
  | some next => if _h : next < r ∧ lower ≤ next then blockSeed a lower next else r
termination_by r

theorem blockSeed_step {a : Pattern} {lower r next : Nat}
    (pred : predecessor a r = some next) (smaller : next < r) (inside : lower ≤ next) :
    blockSeed a lower r = blockSeed a lower next := by
  rw [blockSeed, pred]
  simp only [dif_pos (show next < r ∧ lower ≤ next from ⟨smaller, inside⟩)]

theorem blockSeed_stop {a : Pattern} {lower r next : Nat}
    (pred : predecessor a r = some next) (outside : next < lower) : blockSeed a lower r = r := by
  rw [blockSeed, pred]
  simp only [dif_neg (show ¬(next < r ∧ lower ≤ next) by omega)]

theorem blockSeed_bounds {a : Pattern} {lower r : Nat} (inside : lower ≤ r) :
    lower ≤ blockSeed a lower r ∧ blockSeed a lower r ≤ r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rw [blockSeed]
    split
    · exact ⟨inside, le_rfl⟩
    · rename_i next pred
      split
      · rename_i descend
        have bounds := ih next descend.1 descend.2
        exact ⟨bounds.1, bounds.2.trans descend.1.le⟩
      · exact ⟨inside, le_rfl⟩

/-- Every valid vertex in a positive block has a genuine seed row whose
predecessor leaves the block. No absent predecessor is used as a seed. -/
theorem blockSeed_exit {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {lower r : Nat} (positive : 0 < lower) (inside : lower ≤ r) (included : r ≤ a.length) :
    ∃ row p, rowAt a (blockSeed a lower r) = some row ∧ row.p = some p ∧ p < lower := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    obtain ⟨row, atRow⟩ := rowAt_exists (by omega : 0 < r) included
    have ordinary := shapes row (rowAt_mem atRow)
    obtain ⟨p, hp⟩ := fromRight_exists (xs := row.columns) (k := row.step + 1)
      (by omega) (by have := Row.step_lt_length ordinary; omega)
    change row.p = some p at hp
    have pred : predecessor a r = some p := by simp [predecessor, atRow, hp]
    have smaller := predecessor_lt valid shapes pred
    by_cases stays : lower ≤ p
    · rw [blockSeed_step pred smaller stays]
      exact ih p smaller stays (by omega)
    · rw [blockSeed_stop pred (by omega)]
      exact ⟨row, p, atRow, hp, by omega⟩

/-- A seed is itself fixed by the same entrance-chain construction. -/
theorem blockSeed_idempotent {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {lower r : Nat} (positive : 0 < lower) (inside : lower ≤ r) (included : r ≤ a.length) :
    blockSeed a lower (blockSeed a lower r) = blockSeed a lower r := by
  obtain ⟨row, p, atRow, hp, outside⟩ := blockSeed_exit valid shapes positive inside included
  apply blockSeed_stop (next := p) _ outside
  simp [predecessor, atRow, hp]

/-- Every nonterminal factor on one in-block p chain has the same seed.
The terminal paired source is deliberately excluded from this assertion. -/
theorem FactorTrace.blockSeed_eq {a : Pattern} {lower target start : Nat} {rows : List Nat}
    (h : FactorTrace a target start rows) (inside : ∀ i ∈ rows, lower ≤ i) :
    ∀ i ∈ rows, blockSeed a lower i = blockSeed a lower start := by
  induction h with
  | single pred less =>
    intro i member
    have same := List.mem_singleton.mp member
    subst i
    rfl
  | @cons start next rows pred less inner ih =>
    have innerInside : ∀ i ∈ rows, lower ≤ i := fun i member => inside i (List.mem_cons_of_mem start member)
    have same := blockSeed_step pred less (innerInside next inner.start_mem)
    intro i member
    rcases List.mem_cons.mp member with equal | old
    · subst i; rfl
    · exact (ih innerInside i old).trans same.symm

/-- Seed computation commutes with any strict relabeling that retains
the original p edges. Intermediate inserted vertices cannot intervene. -/
theorem blockSeed_image {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {names : Nat → Nat} (increasing : StrictMono names)
    (edges : ∀ i p, predecessor a i = some p → predecessor b (names i) = some (names p))
    {lower r : Nat} (positive : 0 < lower) (inside : lower ≤ r) (included : r ≤ a.length) :
    blockSeed b (names lower) (names r) = names (blockSeed a lower r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    obtain ⟨row, atRow⟩ := rowAt_exists (by omega : 0 < r) included
    have ordinary := shapes row (rowAt_mem atRow)
    obtain ⟨p, hp⟩ := fromRight_exists (xs := row.columns) (k := row.step + 1)
      (by omega) (by have := Row.step_lt_length ordinary; omega)
    change row.p = some p at hp
    have pred : predecessor a r = some p := by simp [predecessor, atRow, hp]
    have smaller := predecessor_lt valid shapes pred
    by_cases stays : lower ≤ p
    · rw [blockSeed_step pred smaller stays,
        blockSeed_step (edges r p pred) (increasing smaller) (increasing.monotone stays)]
      exact ih p smaller stays (by omega)
    · have outside : p < lower := by omega
      rw [blockSeed_stop pred outside, blockSeed_stop (edges r p pred) (increasing outside)]

end IBLP
