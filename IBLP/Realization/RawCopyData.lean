import IBLP.Realization.RawCopyGeometry
import IBLP.Realization.RetainedRowGraph
import IBLP.Realization.RowGraphData

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

noncomputable def rawCopyRowGraphData (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p : Nat} (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
    (hm : last.columns.head? = some minimum) (hp : last.p = some p)
    (r : FiniteRowIndex b) (row : IBLP.Row) (hr : rowAt b r.val = some row) :
    RowGraphData (D.lastExtension nonempty).next (D.copyPoint nonempty p) r.val row := by
  by_cases old : r.val < a.length
  · let source : FiniteRowIndex a := ⟨r.val, r.property.1, old.le⟩
    have atSource : rowAt a r.val = some row := (IBLP.rawCopy_prefix copy old).symm.trans hr
    exact {
      graph := D.retainedRowGraph nonempty source old
      elementary := fun _ he => D.retainedRow_copy_elementary nonempty p source old atSource he
      critical := fun _ hc => D.retainedRow_copy_critical nonempty p source old atSource hc
      edges := D.retainedRow_copy_edges nonempty p source old atSource }
  · have origin := IBLP.rawCopy_row_origin copy hlast hp (show a.length ≤ r.val by omega) hr
    let source := origin.choose
    have tail : p ≤ source := origin.choose_spec.1
    have owner : r.val = source + (a.length - p) := origin.choose_spec.2.2.1
    have rowCopy : IBLP.copyRow a last source = some row := origin.choose_spec.2.2.2
    have decoded := Option.bind_eq_some_iff.mp rowCopy
    let oldRow := decoded.choose
    have atSource : rowAt a source = some oldRow := decoded.choose_spec.1
    exact {
      graph := (D.lastExtension nonempty).embedding (D.graph (rowIndex atSource))
      elementary := by
        intro e he
        rw [owner]
        exact D.copyRow_graph_elementary nonempty (IBLP.getLast_rowAt hlast) hm hp atSource tail rowCopy he
      critical := fun _ hc => D.copyRow_graph_critical nonempty (IBLP.getLast_rowAt hlast)
        hm hp atSource rowCopy hc
      edges := by
        intro edge member
        rw [owner] at member
        exact D.copyRow_graph_edges nonempty (IBLP.getLast_rowAt hlast) hm hp atSource tail rowCopy edge member }

noncomputable def rawCopyTheta (nonempty : 0 < a.length) (p : Nat) (b : IBLP.Pattern) :
    Fin (b.length + 2) → Ordinal.{u} := fun i => D.copyPoint nonempty p i.val

theorem rawCopyTheta_at (nonempty : 0 < a.length) (p : Nat) (b : IBLP.Pattern)
    (i : Nat) (bound : i ≤ b.length + 1) :
    finiteThetaExtension (D.rawCopyTheta nonempty p b) i = D.copyPoint nonempty p i := by
  simp only [finiteThetaExtension, Nat.min_eq_left bound, rawCopyTheta]

/-- Complete point and row-graph data after the actual raw-copy program.
The parent's proper marks discharge geometric preservation; saturation and
the new weak mark certificates remain separate closure obligations. -/
noncomputable def rawCopyData (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p : Nat} (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p) :
    FiniteBoundedData (D.lastExtension nonempty).next b := by
  have geometry := D.rawCopy_geometry proper copy
  have pred : IBLP.predecessor a a.length = some p := by simp [IBLP.predecessor, IBLP.getLast_rowAt hlast, hp]
  have length := IBLP.rawCopy_length copy hlast hp
  let chosen (r : FiniteRowIndex b) : IBLP.Row := (rowAt_exists r.property.1 r.property.2).choose
  have atChosen (r : FiniteRowIndex b) : rowAt b r.val = some (chosen r) :=
    (rowAt_exists r.property.1 r.property.2).choose_spec
  let rows (r : FiniteRowIndex b) :
      RowGraphData (D.lastExtension nonempty).next
        (finiteThetaExtension (D.rawCopyTheta nonempty p b)) r.val (chosen r) :=
    (D.rawCopyRowGraphData nonempty copy hlast hm hp r (chosen r) (atChosen r)).repoint
      (geometry.1 _ _ (atChosen r)) (geometry.2.1 _ (rowAt_mem (atChosen r)))
      (fun i hi => (D.rawCopyTheta_at nonempty p b i (by have := r.property.2; omega)).symm)
  refine {
    theta := D.rawCopyTheta nonempty p b
    increasing := ?_
    inaccessible := fun i => D.copyPoint_inaccessible nonempty p i.val
    valid := geometry.1
    shapes := geometry.2.1
    graph := fun r => (rows r).graph
    elementary := ?_
    critical := ?_
    edges := ?_ }
  · intro i k less
    apply D.copyPoint_increasing nonempty pred
    · change i.val ≤ a.length + (a.length - p) + 1
      rw [← length]
      have := i.isLt
      omega
    · change k.val ≤ a.length + (a.length - p) + 1
      rw [← length]
      have := k.isLt
      omega
    · exact less
  · intro r
    obtain ⟨row, hr, he⟩ := finiteRow_endpoint_exists geometry.2.1 r
    have same : row = chosen r := Option.some.inj (hr.symm.trans (atChosen r))
    subst row
    exact (rows r).elementary (rowEndpoint b r.val) he
  · intro r row minimum hr hm
    have same : row = chosen r := Option.some.inj (hr.symm.trans (atChosen r))
    subst row
    exact (rows r).critical minimum hm
  · intro r row hr edge member
    have same : row = chosen r := Option.some.inj (hr.symm.trans (atChosen r))
    subst row
    exact (rows r).edges edge member

theorem rawCopyData_top (nonempty : 0 < a.length) {b : IBLP.Pattern} {last : IBLP.Row}
    {minimum p : Nat} (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
    (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p) :
    (D.rawCopyData nonempty proper copy hlast hm hp).top =
      stage.ordinalImage (D.lastExtension nonempty).embedding D.top := by
  change D.copyPoint nonempty p (b.length + 1) = _
  rw [IBLP.rawCopy_length copy hlast hp]
  apply D.copyPoint_top nonempty
  simp [IBLP.predecessor, IBLP.getLast_rowAt hlast, hp]

end IBLP.FiniteBoundedData
