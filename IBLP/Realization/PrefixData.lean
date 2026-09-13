import IBLP.PrefixGeometry
import IBLP.Realization.BoundedRealization

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

def takeTheta (k : Nat) : Fin ((a.take k).length + 2) → Ordinal.{u} := fun i => D.point i.val

theorem takeTheta_at (k i : Nat) (bound : i ≤ (a.take k).length + 1) :
    finiteThetaExtension (D.takeTheta k) i = D.point i := by
  simp only [finiteThetaExtension, Nat.min_eq_left bound, takeTheta]

def takeRowIndex (k : Nat) (r : FiniteRowIndex (a.take k)) : FiniteRowIndex a :=
  ⟨r.val, r.property.1, r.property.2.trans (by simp only [List.length_take]; omega)⟩

/-- A finite prefix keeps the actual saved graphs, including each retained
row's implicit endpoint. It only shortens the finite list of named points. -/
noncomputable def takeData (k : Nat) : FiniteBoundedData stage (a.take k) where
  theta := D.takeTheta k
  increasing := by
    intro i j less
    apply D.point_increasing
    · change i.val ≤ a.length + 1
      have := i.isLt
      simp only [List.length_take] at this
      omega
    · change j.val ≤ a.length + 1
      have := j.isLt
      simp only [List.length_take] at this
      omega
    · exact less
  inaccessible := fun i => D.point_inaccessible i.val
  valid := D.valid.take k
  shapes := D.shapes.take k
  graph := fun r => D.graph (takeRowIndex k r)
  elementary := by
    intro r
    obtain ⟨row, hr, he⟩ := finiteRow_endpoint_exists (D.shapes.take k) r
    have old := IBLP.take_row_origin hr
    have eb := fromRight_le_last (D.valid _ _ old).1 (D.valid _ _ old).2.2.1
      (Row.step_pos (D.shapes row (rowAt_mem old))) he
    rw [D.takeTheta_at k _ (eb.trans (by have := r.property.2; omega)),
      D.takeTheta_at k _ (by have := r.property.2; omega)]
    have saved := D.elementary (takeRowIndex k r)
    change stage.InternalGraphElementary (D.point (rowEndpoint a r.val))
      (D.point (r.val + 1)) (D.graph (takeRowIndex k r)) at saved
    rw [rowEndpoint_eq old he] at saved
    exact saved
  critical := by
    intro r row minimum hr hm
    have old := IBLP.take_row_origin hr
    have member : minimum ∈ row.columns := by
      obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp
        (show row.columns[0]? = some minimum by simpa only [List.head?_eq_getElem?] using hm)
      exact List.mem_iff_getElem.mpr ⟨0, bound, value⟩
    have cb := Row.column_le_last (D.valid _ _ old) member
    rw [D.takeTheta_at k _ (by have := r.property.2; omega)]
    exact D.critical (takeRowIndex k r) row minimum old hm
  edges := by
    intro r row hr edge member
    have old := IBLP.take_row_origin hr
    have bounds := Row.edge_index_bounds (D.valid _ _ old) member
    rw [D.takeTheta_at k _ (by have := r.property.2; omega),
      D.takeTheta_at k _ (by have := r.property.2; omega)]
    exact D.edges (takeRowIndex k r) row old edge member

theorem takeData_point (k i : Nat) (bound : i ≤ (a.take k).length + 1) :
    (D.takeData k).point i = D.point i := D.takeTheta_at k i bound

theorem takeData_graph (k : Nat) (r : FiniteRowIndex (a.take k)) :
    (D.takeData k).graph r = D.graph (takeRowIndex k r) := rfl

theorem takeData_top (k : Nat) : (D.takeData k).top = D.point ((a.take k).length + 1) := rfl

end IBLP.FiniteBoundedData
