import IBLP.BlockSeed
import IBLP.ScanLabels

namespace IBLP

/-- The exact remaining component induction invariant: each nonempty
record in a block inherits the width of an actual nonempty record at its
entrance p-chain seed. This definition does not assert that the invariant
already holds for all actual scans. -/
def SeedRecordHistory (initial : Pattern) (lower upper : Nat) (rec : Records) (names : Nat → Nat) : Prop :=
  ∀ i sources, lower ≤ i → i < upper → (names i, sources) ∈ rec →
    ∃ seedSources, (names (blockSeed initial lower i), seedSources) ∈ rec ∧ sources.length = seedSources.length

theorem SeedRecordHistory.empty (initial : Pattern) (lower upper : Nat) (names : Nat → Nat) :
    SeedRecordHistory initial lower upper [] names := by
  intro i sources _ _ member
  simp at member

/-- The actual neighboring labels determine the width of every record
at a fixed owner, without needing any separate record table assumption. -/
theorem ScanLabeledReach.record_width_unique {initial current : Pattern} {start oldCursor owner : Nat}
    {rec : Records} {names : Nat → Nat} {left right : List Nat}
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (leftRecord : (owner, left) ∈ rec) (rightRecord : (owner, right) ∈ rec) : left.length = right.length := by
  obtain ⟨i, _, _, atI, nextI⟩ := reach.record_neighbors leftRecord
  obtain ⟨j, _, _, atJ, nextJ⟩ := reach.record_neighbors rightRecord
  have same : i = j := reach.names_strictMono.injective (atI.trans atJ.symm)
  subst j
  omega

theorem SeedRecordHistory.same_width {initial current : Pattern} {start oldCursor lower upper i j : Nat}
    {rec : Records} {names : Nat → Nat} {left right : List Nat}
    (history : SeedRecordHistory initial lower upper rec names)
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (iLower : lower ≤ i) (iUpper : i < upper) (jLower : lower ≤ j) (jUpper : j < upper)
    (same : blockSeed initial lower i = blockSeed initial lower j)
    (leftRecord : (names i, left) ∈ rec) (rightRecord : (names j, right) ∈ rec) :
    left.length = right.length := by
  obtain ⟨leftSeed, leftAt, leftWidth⟩ := history i left iLower iUpper leftRecord
  obtain ⟨rightSeed, rightAt, rightWidth⟩ := history j right jLower jUpper rightRecord
  rw [same] at leftAt
  exact leftWidth.trans ((reach.record_width_unique leftAt rightAt).trans rightWidth.symm)

end IBLP
