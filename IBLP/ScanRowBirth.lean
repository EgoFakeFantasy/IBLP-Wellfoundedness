import IBLP.ScanUnprocessedRows

namespace IBLP

/-- Recover the actual native event for any processed entrance row,
including rows that stored no record. Earlier labels are fixed, its
family interval is exact, and the whole completed prefix is untouched. -/
theorem ScanLabeledReach.processed_step {initial current : Pattern}
    {start oldCursor i : Nat} {rec : Records} {names : Nat → Nat}
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (scanned : start ≤ i) (processed : i < oldCursor) :
    ∃ before history after sources birthNames,
      ScanLabeledReach initial start before history i birthNames ∧
      native (completeFrozenMarks before history (birthNames i)) (birthNames i) = some (after, sources) ∧
      (∀ j, j ≤ i → birthNames j = names j) ∧
      names (i + 1) = names i + sources.length + 1 ∧
      (∀ j, j ≤ names i + sources.length → rowAt current j = rowAt after j) := by
  induction reach with
  | start => omega
  | @next before after records old name sources previous bound run ih =>
    by_cases last : i = old
    · subst i
      refine ⟨before, records, after, sources, name, previous, run, ?_, ?_, fun _ _ => rfl⟩
      · intro j before
        have order := previous.names_strictMono.monotone before
        simp only [Function.comp_apply, shiftAfter, if_neg (by omega : ¬ name old < name j)]
      · rw [previous.next_cursor]
        simp only [Function.comp_apply, shiftAfter, if_neg (Nat.lt_irrefl _)]
    · have beforeOld : i < old := by omega
      obtain ⟨eventBefore, eventHistory, eventAfter, eventSources, eventNames,
        event, birth, labels, neighbors, unchanged⟩ := ih (by omega)
      have atI := previous.names_strictMono beforeOld
      have atNext := previous.names_strictMono.monotone (by omega : i + 1 ≤ old)
      refine ⟨eventBefore, eventHistory, eventAfter, eventSources, eventNames, event, birth, ?_, ?_, ?_⟩
      · intro j beforeI
        have order := previous.names_strictMono (show j < old by omega)
        simp only [Function.comp_apply, shiftAfter, if_neg (by omega : ¬ name old < name j)]
        exact labels j beforeI
      · simpa only [Function.comp_apply, shiftAfter, if_neg (by omega : ¬ name old < name (i + 1)),
          if_neg (by omega : ¬ name old < name i)] using neighbors
      · intro j inFamily
        simp only [Function.comp_apply, shiftAfter, if_neg (by omega : ¬ name old < name i)] at inFamily
        have beforeCursor : j < name old := by omega
        rw [native_prefix_rowAt run beforeCursor,
          completeFrozenMarks_other_row (by omega : j ≠ name old)]
        exact unchanged j inFamily

end IBLP
