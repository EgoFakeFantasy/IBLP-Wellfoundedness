import IBLP.Realization.NativeGraphExact
import IBLP.Model.RepresentedAction

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
  (sourcesRun : IBLP.nativeSources a r.val = some sources) (proper : IBLP.ProperMarks a)
  {b : IBLP.Pattern} (run : IBLP.native a r.val = some (b, sources))

theorem nativeData_action_family (i : FiniteRowIndex b) (lower : r.val ≤ i.val)
    (upper : i.val ≤ r.val + sources.length) :
    (D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows.actions.action i.val =
      stage.boundedCutAction (D.point_limit (nativeDomainIndex r sources (i.val - r.val)))
        (D.nativeFamilyMap r hr hp he sourcesRun (i.val - r.val)) := by
  rw [(D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.action_valid]
  exact ModelStage.representedCutAction_congr
    ((D.nativeData r hr hp he sourcesRun proper run).graph_represents i)
    (D.nativeFamilyGraph_represents r hr hp he sourcesRun (i.val - r.val))
    (D.nativeData_graph_family r hr hp he sourcesRun proper run i lower upper) _ _

theorem nativeData_family_restriction (i : FiniteRowIndex b) (lower : r.val ≤ i.val)
    (upper : i.val ≤ r.val + sources.length) :
    CutRestriction ((D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows.actions.action i.val)
      (D.toFiniteTraceRows.toInternalTraceRows.actions.action r.val) := by
  rw [D.nativeData_action_family r hr hp he sourcesRun proper run i lower upper, D.toFiniteTraceRows.action_valid]
  exact D.nativeFamilyMap_restriction r hr hp he sourcesRun (i.val - r.val)

theorem nativeData_row_restriction (i : FiniteRowIndex a) (s : FiniteRowIndex b)
    (owner : s.val = IBLP.shiftAfter r.val sources.length i.val) :
    CutRestriction
      ((D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows.actions.action s.val)
      (D.toFiniteTraceRows.toInternalTraceRows.actions.action i.val) := by
  by_cases before : i.val < r.val
  · have shifted : s.val = i.val := by simpa only [IBLP.shiftAfter, if_neg (by omega : ¬ r.val < i.val)] using owner
    have graph := D.nativeData_graph_prefix r hr hp he sourcesRun proper run s (by omega)
    have indexEq : (⟨s.val, s.property.1, (by have := r.property.2; omega : s.val ≤ a.length)⟩ : FiniteRowIndex a) = i :=
      Subtype.ext shifted
    rw [indexEq] at graph
    rw [← D.rowAction_congr_graphs (D.nativeData r hr hp he sourcesRun proper run) i s graph.symm]
    exact CutRestriction.refl _
  by_cases same : i.val = r.val
  · have shifted : s.val = r.val := by simp only [IBLP.shiftAfter, same, Nat.lt_irrefl, if_false] at owner; exact owner
    have indexEq : i = r := Subtype.ext same
    rw [indexEq]
    exact D.nativeData_family_restriction r hr hp he sourcesRun proper run s (by omega) (by omega)
  · have after : r.val < i.val := by omega
    have shifted : s.val = i.val + sources.length := by simpa only [IBLP.shiftAfter, if_pos after] using owner
    have graph := D.nativeData_graph_suffix r hr hp he sourcesRun proper run s (by omega)
    have indexEq : (⟨s.val - sources.length, (by omega : 0 < s.val - sources.length),
        (by have := i.property.2; omega : s.val - sources.length ≤ a.length)⟩ : FiniteRowIndex a) = i :=
      Subtype.ext (by change s.val - sources.length = i.val; omega)
    rw [indexEq] at graph
    rw [← D.rowAction_congr_graphs (D.nativeData r hr hp he sourcesRun proper run) i s graph.symm]
    exact CutRestriction.refl _

theorem nativeData_family_allInputs (i k : FiniteRowIndex b) (lower : r.val ≤ i.val)
    (less : i.val < k.val) (upper : k.val ≤ r.val + sources.length) :
    CutAction.AllInputAgreement
      ((D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows.actions.action k.val)
      ((D.nativeData r hr hp he sourcesRun proper run).toFiniteTraceRows.toInternalTraceRows.actions.action i.val)
      ((D.nativeData r hr hp he sourcesRun proper run).point (i.val + 1)) := by
  rw [D.nativeData_action_family r hr hp he sourcesRun proper run k (by omega) upper,
    D.nativeData_action_family r hr hp he sourcesRun proper run i lower (by omega),
    D.nativeData_point r hr hp he sourcesRun proper run (i.val + 1) (by have := i.property.2; omega)]
  have value := D.nativeFamilyMap_allInputs r hr hp he sourcesRun (i.val - r.val) (k.val - r.val) (by omega) (by omega)
  have position : r.val + (i.val - r.val) + 1 = i.val + 1 := by omega
  simpa only [position] using value

end IBLP.FiniteBoundedData
