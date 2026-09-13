import IBLP.Realization.FamilyRestrictionHistory
import IBLP.LabelIntervals

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u

/-- Actual native graph construction preserves the full historical
restriction invariant, including each freshly created family row. -/
theorem FamilyRestrictionHistory.native
    {stage : ModelStage.{u}} {initial a b : IBLP.Pattern}
    {D : FiniteBoundedData stage initial} {E : FiniteBoundedData stage a}
    {names : Nat → Nat} {cursor : Nat}
    (history : D.FamilyRestrictionHistory E names)
    (increasing : StrictMono names) (consecutive : names (cursor + 1) = names cursor + 1)
    (r : FiniteRowIndex a) (owner : r.val = names cursor)
    {row : IBLP.Row} {p e : Nat} {sources : List Nat}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (sourcesRun : IBLP.nativeSources a r.val = some sources) (proper : IBLP.ProperMarks a)
    (run : IBLP.native a r.val = some (b, sources)) :
    D.FamilyRestrictionHistory (E.nativeData r hr hp he sourcesRun proper run)
      (IBLP.shiftAfter r.val sources.length ∘ names) := by
  intro i j lower upper
  have intervals := IBLP.label_interval_native increasing consecutive
    (show (IBLP.shiftAfter (names cursor) sources.length ∘ names) i.val ≤ j.val by simpa only [owner] using lower)
    (show j.val < (IBLP.shiftAfter (names cursor) sources.length ∘ names) (i.val + 1) by simpa only [owner] using upper)
  rcases intervals with ⟨old, oldLower, oldUpper, shifted⟩ | ⟨same, familyLower, familyUpper⟩
  · rw [← owner] at shifted
    have length := IBLP.native_length run
    have oldBounds : 0 < old ∧ old ≤ a.length := by
      have jBounds := j.property
      have rBounds := r.property
      unfold IBLP.shiftAfter at shifted
      split at shifted <;> omega
    let oldIndex : FiniteRowIndex a := ⟨old, oldBounds⟩
    exact (E.nativeData_row_restriction r hr hp he sourcesRun proper run oldIndex j shifted).trans
      (history i oldIndex oldLower oldUpper)
  · have oldLower : names i.val ≤ r.val := by rw [same, owner]
    have oldUpper : r.val < names (i.val + 1) := by rw [same, owner, consecutive]; omega
    exact (E.nativeData_family_restriction r hr hp he sourcesRun proper run j
      (by simpa only [owner] using familyLower) (by simpa only [owner] using familyUpper)).trans
      (history i r oldLower oldUpper)

end IBLP.FiniteBoundedData
