import IBLP.RowUpdate
import IBLP.Realization.ShiftRowData

namespace IBLP.FiniteBoundedData
universe u
variable {stage : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData stage a)

def replaceTheta (r : Nat) (out : Row) : Fin ((a.set (r - 1) out).length + 2) → Ordinal.{u} :=
  fun i => D.theta ⟨i.val, by simpa only [List.length_set] using i.isLt⟩

theorem replaceTheta_at (r : Nat) (out : Row) (i : Nat) :
    finiteThetaExtension (D.replaceTheta r out) i = D.point i := by
  simp only [finiteThetaExtension, replaceTheta, point, List.length_set]

def replaceRowIndex (r : Nat) (out : Row) (i : FiniteRowIndex (a.set (r - 1) out)) : FiniteRowIndex a :=
  ⟨i.val, i.property.1, by simpa only [List.length_set] using i.property.2⟩

/-- Replace one row without changing any named point or saved graph.
The new row data must certify that exact graph. -/
noncomputable def replaceData (r : FiniteRowIndex a) {row : Row} (hr : rowAt a r.val = some row)
    (out : Row) (G : RowGraphData stage D.point r.val out) (sameGraph : G.graph = D.graph r)
    (valid : out.BasicValid r.val) (shape : out.OrdinaryShape) :
    FiniteBoundedData stage (a.set (r.val - 1) out) where
  theta := D.replaceTheta r.val out
  increasing := fun i j less => D.increasing (show (⟨i.val, by simpa only [List.length_set] using i.isLt⟩ :
    Fin (a.length + 2)) < ⟨j.val, by simpa only [List.length_set] using j.isLt⟩ from less)
  inaccessible := fun i => D.inaccessible ⟨i.val, by simpa only [List.length_set] using i.isLt⟩
  valid := D.valid.set hr valid
  shapes := D.shapes.set hr shape
  graph := fun i => D.graph (replaceRowIndex r.val out i)
  elementary := by
    intro i
    obtain ⟨current, atCurrent, he⟩ := finiteRow_endpoint_exists (D.shapes.set hr shape) i
    rw [D.replaceTheta_at, D.replaceTheta_at]
    by_cases same : i.val = r.val
    · have sameIndex : replaceRowIndex r.val out i = r := Subtype.ext same
      have eqRow : current = out := by
        rw [same, rowAt_set_self hr] at atCurrent
        exact (Option.some.inj atCurrent).symm
      subst current
      rw [rowEndpoint_eq atCurrent he, sameIndex, same]
      rw [← sameGraph]
      exact G.elementary _ (by simpa only [same] using he)
    · have atOld := (rowAt_set_other hr same).symm.trans atCurrent
      rw [rowEndpoint_eq atCurrent he]
      exact (D.savedRowData (replaceRowIndex r.val out i) atOld).elementary _ he
  critical := by
    intro i current minimum atCurrent hm
    rw [D.replaceTheta_at]
    by_cases same : i.val = r.val
    · have sameIndex : replaceRowIndex r.val out i = r := Subtype.ext same
      have eqRow : current = out := by
        rw [same, rowAt_set_self hr] at atCurrent
        exact (Option.some.inj atCurrent).symm
      subst current
      rw [sameIndex, ← sameGraph]
      exact G.critical minimum hm
    · exact D.critical (replaceRowIndex r.val out i) current minimum
        ((rowAt_set_other hr same).symm.trans atCurrent) hm
  edges := by
    intro i current atCurrent edge member
    rw [D.replaceTheta_at, D.replaceTheta_at]
    by_cases same : i.val = r.val
    · have sameIndex : replaceRowIndex r.val out i = r := Subtype.ext same
      have eqRow : current = out := by
        rw [same, rowAt_set_self hr] at atCurrent
        exact (Option.some.inj atCurrent).symm
      subst current
      rw [same] at member
      rw [sameIndex, ← sameGraph]
      exact G.edges edge member
    · exact D.edges (replaceRowIndex r.val out i) current
        ((rowAt_set_other hr same).symm.trans atCurrent) edge member

theorem replaceData_point (r : FiniteRowIndex a) {row : Row} (hr : rowAt a r.val = some row)
    (out : Row) (G : RowGraphData stage D.point r.val out) (sameGraph : G.graph = D.graph r)
    (valid : out.BasicValid r.val) (shape : out.OrdinaryShape) (i : Nat) :
    (D.replaceData r hr out G sameGraph valid shape).point i = D.point i := D.replaceTheta_at _ _ _

theorem replaceData_top (r : FiniteRowIndex a) {row : Row} (hr : rowAt a r.val = some row)
    (out : Row) (G : RowGraphData stage D.point r.val out) (sameGraph : G.graph = D.graph r)
    (valid : out.BasicValid r.val) (shape : out.OrdinaryShape) :
    (D.replaceData r hr out G sameGraph valid shape).top = D.top := by
  simp only [top, replaceData, replaceTheta, List.length_set]

theorem replaceData_graph (r : FiniteRowIndex a) {row : Row} (hr : rowAt a r.val = some row)
    (out : Row) (G : RowGraphData stage D.point r.val out) (sameGraph : G.graph = D.graph r)
    (valid : out.BasicValid r.val) (shape : out.OrdinaryShape) (i : FiniteRowIndex (a.set (r.val - 1) out)) :
    (D.replaceData r hr out G sameGraph valid shape).graph i = D.graph (replaceRowIndex r.val out i) := rfl

end IBLP.FiniteBoundedData
