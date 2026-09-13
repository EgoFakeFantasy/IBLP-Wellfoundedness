import IBLP.Realization.CopyScanCoverage
import IBLP.Realization.ScanEventInduction
import IBLP.FrozenEmpty

namespace IBLP.BoundedRealization
universe u

/-- Complete semantic closure of every actual copied/cut scan entrance
and its frozen queue. The outer cursor induction discharges all prior-row
geometry; the inner frozen induction discharges all prior-mark geometry.
No scan-history correctness assumptions remain. -/
theorem copies_scan_realizations {stage savedStage : ModelStage.{u}}
    {a copied initial : Pattern} (R : BoundedRealization stage a)
    (entry : MarkedRealization savedStage initial) {last : Row} {p m : Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) :
    ∀ current rec old names, ScanLabeledReach initial a.length current rec old names →
      ∃ S : MarkedRealization savedStage current,
        S.top = entry.top ∧ entry.data.FamilyRestrictionHistory S.data names ∧
        FrozenGeometryBefore current rec (names old) 0 ∧
        ∃ T : MarkedRealization savedStage (completeFrozenMarks current rec (names old)),
          T.top = entry.top ∧ entry.data.FamilyRestrictionHistory T.data names := by
  apply entry.scan_realization_from_frozen_step a.length
  intro current rec old names reach earlierRows S history
  have afterStart := reach.oldCursor_ge_start
  cases atOriginal : rowAt initial old with
  | none =>
    have positive := rowAt_pos (getLast_rowAt hlast)
    have outside : initial.length < old := by
      by_contra reverse
      obtain ⟨row, atRow⟩ := rowAt_exists (by omega : 0 < old) (Nat.le_of_not_gt reverse)
      simp only [atOriginal, reduceCtorEq] at atRow
    have balance := reach.length_balance
    have absent : rowAt current (names old) = none := by
      cases actual : rowAt current (names old) with
      | none => rfl
      | some row => have bound := rowAt_le_length actual; omega
    refine ⟨FrozenGeometryBefore.of_empty_row absent, ?_⟩
    rw [show completeFrozenMarks current rec (names old) = current by simp only [completeFrozenMarks, absent]]
    exact ⟨S, rfl, history⟩
  | some row =>
    obtain ⟨k, within, lower, upper⟩ := R.copies_cut_cursor_block hlast hp copies cut afterStart
      (rowAt_le_length atOriginal)
    exact R.copies_frozen_closure entry S hlast hp copies cut within lower upper atOriginal reach earlierRows history

/-- Syntax for every actual native input is now an output of the complete
semantic induction, rather than an independent history hypothesis. -/
theorem copies_scan_syntax_history {stage savedStage : ModelStage.{u}}
    {a copied initial : Pattern} (R : BoundedRealization stage a)
    (entry : MarkedRealization savedStage initial) {last : Row} {p m : Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) :
    ScanSyntaxHistory initial a.length := by
  intro current rec cursor reach
  obtain ⟨old, names, labeled, atCursor⟩ := reach.labeled
  obtain ⟨_, _, _, _, T, _, _⟩ := R.copies_scan_realizations entry hlast hp copies cut current rec old names labeled
  simpa only [atCursor] using And.intro T.data.valid (And.intro T.data.shapes T.proper)

end IBLP.BoundedRealization
