import IBLP.Realization.FamilyRestrictionHistory
import IBLP.Realization.CompletionRealized
import IBLP.FrozenGeometry

namespace IBLP.MarkedRealization
universe u

set_option maxHeartbeats 1000000 in
/-- Close the whole original frozen queue from a step that consumes only
strictly earlier geometry and the current historical graph invariant.
Strong induction counts processed frozen marks, so the current packet is
never available as its own premise. -/
theorem frozen_realization_from_event_step {stage : ModelStage.{u}} {original initial : Pattern}
    (D : FiniteBoundedData stage original) (R : MarkedRealization stage initial)
    (rec : Records) (owner : Nat) (names : Nat → Nat)
    (entrance : D.FamilyRestrictionHistory R.data names)
    (step : ∀ current mark pending, FrozenReach initial rec owner current (mark :: pending) →
      FrozenGeometryBefore initial rec owner (mark :: pending).length →
      ∀ S : MarkedRealization stage current, D.FamilyRestrictionHistory S.data names →
      ∀ row sources, rowAt current owner = some row → completionRecord current rec owner mark = some sources →
      ∃ C : row.CompletionGeometry owner mark sources, S.data.CompletionHistoryPacket owner mark sources) :
    FrozenGeometryBefore initial rec owner 0 ∧
      ∃ S : MarkedRealization stage (completeFrozenMarks initial rec owner),
        S.top = R.top ∧ D.FamilyRestrictionHistory S.data names := by
  have queueBound : ∀ current pending, FrozenReach initial rec owner current pending →
      pending.length ≤ (frozenMarks initial owner).length := by
    intro current pending reach
    obtain ⟨processed, queue, _⟩ := reach.decomposition
    rw [queue, List.length_append]
    omega
  have prefixes : ∀ fuel current pending, (reach : FrozenReach initial rec owner current pending) →
      (frozenMarks initial owner).length - pending.length = fuel →
      ∃ S : MarkedRealization stage current,
        S.top = R.top ∧ D.FamilyRestrictionHistory S.data names ∧
        (∀ mark rest, pending = mark :: rest → ∀ row sources,
          rowAt current owner = some row → completionRecord current rec owner mark = some sources →
          ∃ C : row.CompletionGeometry owner mark sources, S.data.CompletionHistoryPacket owner mark sources) := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro current pending reach count
      have earlierGeometry : FrozenGeometryBefore initial rec owner pending.length := by
        intro before mark todo previous earlier row sources atRow guard
        have bound := queueBound before (mark :: todo) previous
        obtain ⟨S, _, _, event⟩ := ih ((frozenMarks initial owner).length - (mark :: todo).length)
          (by omega) before (mark :: todo) previous rfl
        obtain ⟨C, _⟩ := event mark todo rfl row sources atRow guard
        exact ⟨C⟩
      have realized : ∃ S : MarkedRealization stage current,
          S.top = R.top ∧ D.FamilyRestrictionHistory S.data names := by
        cases reach with
        | start => exact ⟨R, rfl, entrance⟩
        | @next before mark todo previous =>
          have bound := queueBound before (mark :: pending) previous
          obtain ⟨S, top, history, event⟩ := ih ((frozenMarks initial owner).length - (mark :: pending).length)
            (by simp only [List.length_cons] at *; omega) before (mark :: pending) previous rfl
          cases atRow : rowAt before owner with
          | none =>
            rw [show completeMark before rec owner mark = before by simp only [completeMark, atRow]]
            exact ⟨S, top, history⟩
          | some row =>
            cases guard : completionRecord before rec owner mark with
            | none =>
              rw [show completeMark before rec owner mark = before by simp only [completeMark, atRow, guard]]
              exact ⟨S, top, history⟩
            | some sources =>
              obtain ⟨C, H⟩ := event mark pending rfl row sources atRow guard
              let index : FiniteRowIndex before := ⟨owner, rowAt_pos atRow, rowAt_le_length atRow⟩
              rw [show completeMark before rec owner mark = before.set (owner - 1) (completeMarkRow row mark sources) by
                simp only [completeMark, atRow, guard]]
              refine ⟨S.completion index atRow C H, (S.completion_top index atRow C H).trans top, ?_⟩
              exact history.completion index atRow C (S.proper row (rowAt_mem atRow)) (H.edge S.data)
      obtain ⟨S, top, history⟩ := realized
      refine ⟨S, top, history, ?_⟩
      intro mark todo same row sources atRow guard
      subst pending
      exact step current mark todo reach earlierGeometry S history row sources atRow guard
  refine ⟨?_, ?_⟩
  · intro current mark pending reach _ row sources atRow guard
    obtain ⟨S, _, _, event⟩ := prefixes _ current (mark :: pending) reach rfl
    obtain ⟨C, _⟩ := event mark pending rfl row sources atRow guard
    exact ⟨C⟩
  · obtain ⟨S, top, history, _⟩ := prefixes _ (completeFrozenMarks initial rec owner) []
      (FrozenReach.finish initial rec owner) rfl
    exact ⟨S, top, history⟩

end IBLP.MarkedRealization
