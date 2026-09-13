import IBLP.Realization.NativeFamilyMarks

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)

/-- The original native operation preserves complete marked realization
in the same model, including every accurate mark. Saturation is restored
only by the later frozen scan, as required by the manuscript. -/
noncomputable def native (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat} {b : IBLP.Pattern}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (sourcesRun : IBLP.nativeSources a r.val = some sources) (run : IBLP.native a r.val = some (b, sources)) :
    MarkedRealization stage b where
  data := R.data.nativeData r hr hp he sourcesRun R.proper run
  proper := IBLP.native_preserves_proper R.data.valid R.data.shapes R.proper run
  marks := by
    intro i out mark atOut marked
    by_cases before : i < r.val
    · have atOld : IBLP.rowAt a i = some out := (IBLP.native_prefix_rowAt run before).symm.trans atOut
      exact R.native_prefix_markRealized r hr hp he sourcesRun run atOld before marked
    by_cases family : i ≤ r.val + sources.length
    · obtain ⟨baseRow, block, atBase, _, blockRun, _⟩ := IBLP.native_decomposition run
      have same := Option.some.inj (atBase.symm.trans hr)
      subst baseRow
      have length := IBLP.nativeBlock_length blockRun
      have owner : r.val + (i - r.val) = i := by omega
      have entry : block[i - r.val]? = some out := by
        rw [← IBLP.native_family_rowAt hr run blockRun (by omega), owner]
        exact atOut
      have realized := R.native_family_markRealized r hr hp he sourcesRun run blockRun entry marked
      simpa only [owner] using realized
    · have after : r.val < i - sources.length := by omega
      have owner : i - sources.length + sources.length = i := by omega
      have suffix := IBLP.native_suffix_rowAt run after
      rw [owner, atOut] at suffix
      obtain ⟨oldRow, atOld, rowSame⟩ := Option.map_eq_some_iff.mp suffix.symm
      subst out
      obtain ⟨oldMark, oldMarked, markSame⟩ := List.mem_map.mp marked
      subst mark
      have realized := R.native_suffix_markRealized r hr hp he sourcesRun run atOld after oldMarked
      simpa only [owner] using realized

theorem native_top (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat} {b : IBLP.Pattern}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (sourcesRun : IBLP.nativeSources a r.val = some sources) (run : IBLP.native a r.val = some (b, sources)) :
    (R.native r hr hp he sourcesRun run).top = R.top :=
  R.data.nativeData_top r hr hp he sourcesRun R.proper run

/-- No auxiliary source, domain or certificate assumptions are required
by the semantic closure statement for an actual successful native step. -/
theorem native_realization_exists {r : Nat} {b : IBLP.Pattern} {sources : List Nat}
    (run : IBLP.native a r = some (b, sources)) :
    ∃ S : MarkedRealization stage b, S.top = R.top := by
  obtain ⟨row, _, hr, sourcesRun, _, _⟩ := IBLP.native_decomposition run
  let index : FiniteRowIndex a := ⟨r, rowAt_pos hr, rowAt_le_length hr⟩
  have shape := R.data.shapes row (rowAt_mem hr)
  have positive := IBLP.Row.step_pos shape
  have room := IBLP.Row.step_lt_length shape
  obtain ⟨p, hp⟩ := IBLP.fromRight_exists (xs := row.columns) (k := row.step + 1) (by omega) (by omega)
  obtain ⟨e, he⟩ := IBLP.fromRight_exists (xs := row.columns) (k := row.step) positive room.le
  exact ⟨R.native index hr hp he sourcesRun run, R.native_top index hr hp he sourcesRun run⟩

theorem native_total_realized {r : Nat} {row : IBLP.Row} (hr : IBLP.rowAt a r = some row) :
    ∃ b sources, IBLP.native a r = some (b, sources) ∧ ∃ S : MarkedRealization stage b, S.top = R.top := by
  obtain ⟨b, sources, run⟩ := IBLP.native_total R.data.valid R.data.shapes hr
  exact ⟨b, sources, run, R.native_realization_exists run⟩

end IBLP.MarkedRealization
