import IBLP.SeedRecordHistory

namespace IBLP

theorem shiftAfter_fixed_of_image_le {cursor width point : Nat}
    (below : shiftAfter cursor width point ≤ cursor) : shiftAfter cursor width point = point := by
  by_cases above : cursor < point
  · simp only [shiftAfter, if_pos above] at below
    omega
  · simp only [shiftAfter, if_neg above]

/-- The record invariant is preserved by the exact nonempty native record
update once the new record's seed witness is supplied. All old record
owners and seed owners lie in the prefix fixed by this insertion. -/
theorem SeedRecordHistory.native_nonempty {initial current : Pattern}
    {start oldCursor lower upper : Nat} {rec : Records} {names : Nat → Nat} {sources : List Nat}
    (history : SeedRecordHistory initial lower upper rec names)
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (newSeed : lower ≤ oldCursor → oldCursor < upper →
      ∃ saved, (names (blockSeed initial lower oldCursor), saved) ∈ (names oldCursor, sources) :: rec ∧
        sources.length = saved.length) :
    SeedRecordHistory initial lower upper ((names oldCursor, sources) :: rec)
      (shiftAfter (names oldCursor) sources.length ∘ names) := by
  intro i saved lo hi member
  rcases List.mem_cons.mp member with new | old
  · have sameImage := congrArg Prod.fst new
    have sameSources := congrArg Prod.snd new
    change shiftAfter (names oldCursor) sources.length (names i) = names oldCursor at sameImage
    change saved = sources at sameSources
    have fixed := shiftAfter_fixed_of_image_le sameImage.le
    have same : i = oldCursor := reach.names_strictMono.injective (fixed.symm.trans sameImage)
    subst i
    subst saved
    obtain ⟨seedSources, seedRecord, width⟩ := newSeed lo hi
    have seedBound := (blockSeed_bounds (a := initial) lo).2
    have fixedSeed : (shiftAfter (names oldCursor) sources.length ∘ names) (blockSeed initial lower oldCursor) =
        names (blockSeed initial lower oldCursor) := by
      exact reach.processed_names_fixed seedBound
    exact ⟨seedSources, by simpa only [fixedSeed] using seedRecord, width⟩
  · have behind := reach.forget.record_family_before old
    have fixed : (shiftAfter (names oldCursor) sources.length ∘ names) i = names i :=
      shiftAfter_fixed_of_image_le (by change shiftAfter _ _ _ + saved.length < names oldCursor at behind; omega)
    rw [fixed] at old
    obtain ⟨seedSources, seedRecord, width⟩ := history i saved lo hi old
    have seedBehind := reach.forget.record_family_before seedRecord
    have fixedSeed : (shiftAfter (names oldCursor) sources.length ∘ names) (blockSeed initial lower i) =
        names (blockSeed initial lower i) := by
      simp only [Function.comp_apply, shiftAfter, if_neg (by omega : ¬ names oldCursor < names (blockSeed initial lower i))]
    exact ⟨seedSources, by rw [fixedSeed]; exact List.mem_cons_of_mem _ seedRecord, width⟩

theorem SeedRecordHistory.native_step {initial current : Pattern}
    {start oldCursor lower upper : Nat} {rec : Records} {names : Nat → Nat} {sources : List Nat}
    (history : SeedRecordHistory initial lower upper rec names)
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (newSeed : sources ≠ [] → lower ≤ oldCursor → oldCursor < upper →
      ∃ saved, (names (blockSeed initial lower oldCursor), saved) ∈ (names oldCursor, sources) :: rec ∧
        sources.length = saved.length) :
    SeedRecordHistory initial lower upper (if sources.isEmpty then rec else (names oldCursor, sources) :: rec)
      (shiftAfter (names oldCursor) sources.length ∘ names) := by
  by_cases empty : sources = []
  · subst sources
    have same : shiftAfter (names oldCursor) 0 ∘ names = names := by
      funext i
      simp [Function.comp_apply, shiftAfter]
    simpa only [List.isEmpty_nil, if_true, List.length_nil, same] using history
  · simpa only [List.isEmpty_iff, empty, if_false] using history.native_nonempty reach (newSeed empty)

end IBLP
