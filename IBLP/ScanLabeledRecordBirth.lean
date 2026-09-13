import IBLP.SeedRecordStep

namespace IBLP

/-- Recover the actual birth of a retained record with its exact source
list and entrance-row index. All labels through that old owner agree
with the current labels, so this transports list contents as well as width. -/
theorem ScanLabeledReach.record_birth {initial current : Pattern}
    {start oldCursor i : Nat} {rec : Records} {names : Nat → Nat} {saved : List Nat}
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (member : (names i, saved) ∈ rec) :
    ∃ before history after birthNames,
      ScanLabeledReach initial start before history i birthNames ∧
      native (completeFrozenMarks before history (birthNames i)) (birthNames i) = some (after, saved) ∧
      (∀ j, j ≤ i → birthNames j = names j) := by
  induction reach with
  | start => simp at member
  | @next before after records old name sources previous bound run ih =>
    have retain (oldMember : ((shiftAfter (name old) sources.length ∘ name) i, saved) ∈ records) :
        ∃ birth history result birthNames,
          ScanLabeledReach initial start birth history i birthNames ∧
          native (completeFrozenMarks birth history (birthNames i)) (birthNames i) = some (result, saved) ∧
          (∀ j, j ≤ i → birthNames j = (shiftAfter (name old) sources.length ∘ name) j) := by
      have behind := previous.forget.record_family_before oldMember
      have fixed : (shiftAfter (name old) sources.length ∘ name) i = name i :=
        shiftAfter_fixed_of_image_le (by change shiftAfter _ _ _ + saved.length < name old at behind; omega)
      rw [fixed] at oldMember
      obtain ⟨birth, history, result, birthNames, atBirth, birthRun, labels⟩ := ih oldMember
      have beforeOwner := previous.forget.record_family_before oldMember
      refine ⟨birth, history, result, birthNames, atBirth, birthRun, ?_⟩
      intro j beforeI
      have order := previous.names_strictMono.monotone beforeI
      simp only [Function.comp_apply, shiftAfter, if_neg (by omega : ¬ name old < name j)]
      exact labels j beforeI
    by_cases empty : sources = []
    · simp only [List.isEmpty_iff, empty, if_true] at member
      exact retain (by simpa only [empty] using member)
    · simp only [List.isEmpty_iff, empty, if_false] at member
      rcases List.mem_cons.mp member with new | oldMember
      · have sameImage := congrArg Prod.fst new
        have sameSources := congrArg Prod.snd new
        change shiftAfter (name old) sources.length (name i) = name old at sameImage
        change saved = sources at sameSources
        have fixed := shiftAfter_fixed_of_image_le sameImage.le
        have same : i = old := previous.names_strictMono.injective (fixed.symm.trans sameImage)
        subst i
        subst saved
        exact ⟨before, records, after, name, previous, run,
          fun j bound => (previous.processed_names_fixed bound).symm⟩
      · exact retain oldMember

end IBLP
