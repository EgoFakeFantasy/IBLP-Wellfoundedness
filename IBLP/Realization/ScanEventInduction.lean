import IBLP.Realization.NativeFamilyHistory
import IBLP.Realization.NativeRealized
import IBLP.ScanGeometryHistory

namespace IBLP.MarkedRealization
universe u

set_option maxHeartbeats 1000000 in
/-- Outer event induction on the actual row cursor. Every earlier
reachable scan is covered, even when its old-label presentation differs.
The local frozen closure therefore receives genuine strictly prior
geometry, and native advances the semantic graph invariant. -/
theorem scan_realization_from_frozen_step {stage : ModelStage.{u}} {initial : Pattern}
    (D : MarkedRealization stage initial) (start : Nat)
    (step : ∀ current rec old names,
      ScanLabeledReach initial start current rec old names →
      ScanPriorGeometry initial start (names old) →
      ∀ S : MarkedRealization stage current, D.data.FamilyRestrictionHistory S.data names →
      FrozenGeometryBefore current rec (names old) 0 ∧
        ∃ T : MarkedRealization stage (completeFrozenMarks current rec (names old)),
          T.top = S.top ∧ D.data.FamilyRestrictionHistory T.data names) :
    ∀ current rec old names, ScanLabeledReach initial start current rec old names →
      ∃ S : MarkedRealization stage current,
        S.top = D.top ∧ D.data.FamilyRestrictionHistory S.data names ∧
        FrozenGeometryBefore current rec (names old) 0 ∧
        ∃ T : MarkedRealization stage (completeFrozenMarks current rec (names old)),
          T.top = D.top ∧ D.data.FamilyRestrictionHistory T.data names := by
  have all : ∀ cursor current rec old names,
      ScanLabeledReach initial start current rec old names → names old = cursor →
      ∃ S : MarkedRealization stage current,
        S.top = D.top ∧ D.data.FamilyRestrictionHistory S.data names ∧
        FrozenGeometryBefore current rec (names old) 0 ∧
        ∃ T : MarkedRealization stage (completeFrozenMarks current rec (names old)),
          T.top = D.top ∧ D.data.FamilyRestrictionHistory T.data names := by
    intro cursor
    induction cursor using Nat.strong_induction_on with
    | h cursor ih =>
      intro current rec old names reach clock
      have prior : ScanPriorGeometry initial start (names old) := by
        intro before records owner previous earlier
        obtain ⟨oldIndex, oldNames, labeled, atOwner⟩ := previous.labeled
        obtain ⟨_, _, _, geometry, _⟩ := ih owner (by omega) before records oldIndex oldNames labeled atOwner
        simpa only [atOwner] using geometry
      have realized : ∃ S : MarkedRealization stage current,
          S.top = D.top ∧ D.data.FamilyRestrictionHistory S.data names := by
        cases reach with
        | start => exact ⟨D, rfl, FiniteBoundedData.FamilyRestrictionHistory.refl D.data⟩
        | @next before after records oldIndex oldNames sources previous bound run =>
          have earlier : oldNames oldIndex < cursor := by
            rw [previous.next_cursor] at clock
            omega
          obtain ⟨_, _, _, _, T, top, history⟩ :=
            ih (oldNames oldIndex) earlier before records oldIndex oldNames previous rfl
          obtain ⟨row, _, atRow, sourcesRun, _, _⟩ := native_decomposition run
          let index : FiniteRowIndex (completeFrozenMarks before records (oldNames oldIndex)) :=
            ⟨oldNames oldIndex, rowAt_pos atRow, rowAt_le_length atRow⟩
          have shape := T.data.shapes row (rowAt_mem atRow)
          obtain ⟨p, hp⟩ := fromRight_exists (xs := row.columns) (k := row.step + 1)
            (by omega) (by have := Row.step_lt_length shape; omega)
          obtain ⟨e, he⟩ := fromRight_exists (xs := row.columns) (k := row.step)
            (Row.step_pos shape) (Row.step_lt_length shape).le
          have consecutive : oldNames (oldIndex + 1) = oldNames oldIndex + 1 := by
            have balance := previous.suffix_balance (oldIndex + 1) (Nat.le_succ _)
            omega
          refine ⟨T.native index atRow hp he sourcesRun run,
            (T.native_top index atRow hp he sourcesRun run).trans top, ?_⟩
          exact history.native previous.names_strictMono consecutive index rfl
            atRow hp he sourcesRun T.proper run
      obtain ⟨S, top, history⟩ := realized
      obtain ⟨geometry, T, frozenTop, frozenHistory⟩ := step current rec old names reach prior S history
      exact ⟨S, top, history, geometry, T, frozenTop.trans top, frozenHistory⟩
  intro current rec old names reach
  exact all (names old) current rec old names reach rfl

end IBLP.MarkedRealization
