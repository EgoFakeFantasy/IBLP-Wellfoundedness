import IBLP.Realization.CompletionMarks
import FullMarkedBLP.CompletionRowClosure

namespace IBLP.MarkedRealization
universe u
variable {stage : ModelStage.{u}} {a : Pattern} (R : MarkedRealization stage a)

/-- Local completion closure from the packet geometry and complete
parallel-history certificates. Both premises must still be obtained
from strictly earlier scan events in the manuscript's joint induction. -/
noncomputable def completion (r : FiniteRowIndex a) {row : Row} {mark : Nat} {sources : List Nat}
    (hr : rowAt a r.val = some row) (C : row.CompletionGeometry r.val mark sources)
    (H : R.data.CompletionHistoryPacket r.val mark sources) :
    MarkedRealization stage (a.set (r.val - 1) (completeMarkRow row mark sources)) where
  data := R.data.completionData r hr C (R.proper row (rowAt_mem hr)) (H.edge R.data)
  proper := (C.set_syntax R.data.valid R.data.shapes R.proper hr).2.2
  marks := by
    intro i out z atOut marked
    by_cases same : i = r.val
    · subst i
      have eqRow : out = completeMarkRow row mark sources := by
        rw [rowAt_set_self hr] at atOut
        exact (Option.some.inj atOut).symm
      subst out
      simp only [completeMarkRow, mem_canonicalColumns, List.mem_append] at marked
      rcases marked with old | new
      · exact R.completion_old_markRealized r hr C (H.edge R.data) (List.mem_filter.mp old).1
      · obtain ⟨j, hj, eq⟩ := List.mem_map.mp new
        obtain ⟨s, member, rank⟩ := FullMarkedBLP.exists_source_at_rank C.distinct (List.mem_range.mp hj)
        have value := R.completion_new_markRealized r hr C (H.edge R.data) H member
        have target : mark + 1 + (sources.filter (· < s)).length = z := by omega
        simpa only [target] using value
    · have atOld := (rowAt_set_other hr same).symm.trans atOut
      exact R.completion_other_markRealized r hr C (H.edge R.data) atOld same marked

theorem completion_top (r : FiniteRowIndex a) {row : Row} {mark : Nat} {sources : List Nat}
    (hr : rowAt a r.val = some row) (C : row.CompletionGeometry r.val mark sources)
    (H : R.data.CompletionHistoryPacket r.val mark sources) :
    (R.completion r hr C H).top = R.top :=
  R.data.completionData_top r hr C (R.proper row (rowAt_mem hr)) (H.edge R.data)

/-- Exact conditional closure for the actual guarded operation. This
states the remaining packet obligation explicitly and leaves all guard
failures as the original no-op. -/
theorem completeMark_realization_of_packets (rec : Records) (r mark : Nat)
    (events : ∀ row sources, rowAt a r = some row → completionRecord a rec r mark = some sources →
      ∃ C : row.CompletionGeometry r mark sources, R.data.CompletionHistoryPacket r mark sources) :
    ∃ S : MarkedRealization stage (completeMark a rec r mark), S.top = R.top := by
  cases hr : rowAt a r with
  | none =>
    rw [show completeMark a rec r mark = a by simp only [completeMark, hr]]
    exact ⟨R, rfl⟩
  | some row =>
    cases record : completionRecord a rec r mark with
    | none =>
      rw [show completeMark a rec r mark = a by simp only [completeMark, hr, record]]
      exact ⟨R, rfl⟩
    | some sources =>
      obtain ⟨C, H⟩ := events row sources hr record
      let index : FiniteRowIndex a := ⟨r, rowAt_pos hr, rowAt_le_length hr⟩
      rw [show completeMark a rec r mark = a.set (r - 1) (completeMarkRow row mark sources) by
        simp only [completeMark, hr, record]]
      exact ⟨R.completion index hr C H, R.completion_top index hr C H⟩

end IBLP.MarkedRealization
