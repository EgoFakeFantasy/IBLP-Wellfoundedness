import IBLP.Realization.NativeActions
import IBLP.Realization.CompletionData
import IBLP.Rank.RestrictionTrans

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {initial a b : IBLP.Pattern}

/-- Every actual row between two consecutive old labels is a restriction
of the saved entrance graph of its old base. This includes the old base
itself, empty families, and every new family row. -/
def FamilyRestrictionHistory (D : FiniteBoundedData stage initial) (E : FiniteBoundedData stage a)
    (names : Nat → Nat) : Prop :=
  ∀ i : FiniteRowIndex initial, ∀ j : FiniteRowIndex a,
    names i.val ≤ j.val → j.val < names (i.val + 1) →
    CutRestriction (E.toFiniteTraceRows.toInternalTraceRows.actions.action j.val)
      (D.toFiniteTraceRows.toInternalTraceRows.actions.action i.val)

theorem FamilyRestrictionHistory.refl (D : FiniteBoundedData stage initial) :
    D.FamilyRestrictionHistory D id := by
  intro i j lower upper
  have same : j = i := Subtype.ext (by simp only [id_eq] at *; omega)
  subst j
  exact CutRestriction.refl _

theorem FamilyRestrictionHistory.completion
    {D : FiniteBoundedData stage initial} {E : FiniteBoundedData stage a} {names : Nat → Nat}
    (history : D.FamilyRestrictionHistory E names)
    (r : FiniteRowIndex a) {row : IBLP.Row} {mark : Nat} {sources : List Nat}
    (hr : IBLP.rowAt a r.val = some row) (C : row.CompletionGeometry r.val mark sources)
    (proper : ∀ z ∈ row.marks, row.ProperMark z)
    (packet : ∀ s ∈ sources, E.nativeImage r s = E.point (mark + 1 + (sources.filter (· < s)).length)) :
    D.FamilyRestrictionHistory (E.completionData r hr C proper packet) names := by
  intro i j lower upper
  let old := replaceRowIndex r.val (IBLP.completeMarkRow row mark sources) j
  have graph := E.completionData_graph r hr C proper packet j
  have action := E.rowAction_congr_graphs (E.completionData r hr C proper packet) old j graph.symm
  rw [← action]
  exact history i old lower upper

end IBLP.FiniteBoundedData
