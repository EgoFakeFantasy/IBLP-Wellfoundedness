import IBLP.Realization.CopyRowGraph

namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem source_le_owner (r : FiniteRowIndex a) : D.source r.val ≤ D.point r.val := by
  obtain ⟨row, hr, he⟩ := finiteRow_endpoint_exists D.shapes r
  have eb := fromRight_le_last (D.valid _ _ hr).1 (D.valid _ _ hr).2.2.1
    (Row.step_pos (D.shapes row (rowAt_mem hr))) he
  rw [D.source_eq hr he]
  exact D.point_increasing.monotoneOn (by change rowEndpoint a r.val ≤ a.length + 1; omega)
    (by change r.val ≤ a.length + 1; have := r.property.2; omega) eb

theorem retainedRow_rank_lt (r : FiniteRowIndex a) (old : r.val < a.length) :
    (D.graph r).val.rank < D.top := by
  have target : D.point (r.val + 1) < D.top := by
    rw [← D.point_top]
    exact D.point_increasing (by change r.val + 1 ≤ a.length + 1; omega)
      (by change a.length + 1 ≤ a.length + 1; omega) (by omega)
  have source : D.source r.val < D.top :=
    (D.source_le_owner r).trans_lt ((D.point_increasing
      (by change r.val ≤ a.length + 1; omega)
      (by change r.val + 1 ≤ a.length + 1; omega) (by omega)).trans target)
  exact Extender.InternalExtension.graph_rank_lt (D.point_top ▸ D.point_limit (a.length + 1))
    (D.source r.val) (D.point (r.val + 1)) source target (D.graph r) (D.elementary r)

noncomputable def retainedRowGraph (nonempty : 0 < a.length) (r : FiniteRowIndex a)
    (old : r.val < a.length) : (D.lastExtension nonempty).next.model.Element :=
  (D.lastExtension nonempty).retain (D.graph r) (D.retainedRow_rank_lt r old)

theorem retainedRow_elementary (nonempty : 0 < a.length) (r : FiniteRowIndex a)
    (old : r.val < a.length) :
    (D.lastExtension nonempty).next.InternalGraphElementary (D.source r.val)
      (D.point (r.val + 1)) (D.retainedRowGraph nonempty r old) := by
  have target : D.point (r.val + 1) < D.top := by
    rw [← D.point_top]
    exact D.point_increasing (by change r.val + 1 ≤ a.length + 1; omega)
      (by change a.length + 1 ≤ a.length + 1; omega) (by omega)
  have source : D.source r.val < D.top :=
    (D.source_le_owner r).trans_lt ((D.point_increasing
      (by change r.val ≤ a.length + 1; omega)
      (by change r.val + 1 ≤ a.length + 1; omega) (by omega)).trans target)
  exact (D.lastExtension nonempty).retained_elementary (D.point_top ▸ D.point_limit (a.length + 1))
    (D.source r.val) (D.point (r.val + 1)) source target (D.graph r) (D.elementary r)

theorem retainedRow_copy_elementary (nonempty : 0 < a.length) (p : Nat) (r : FiniteRowIndex a)
    (old : r.val < a.length) {row : IBLP.Row} {e : Nat}
    (hr : rowAt a r.val = some row) (he : row.e = some e) :
    (D.lastExtension nonempty).next.InternalGraphElementary (D.copyPoint nonempty p e)
      (D.copyPoint nonempty p (r.val + 1)) (D.retainedRowGraph nonempty r old) := by
  have eb := fromRight_le_last (D.valid _ _ hr).1 (D.valid _ _ hr).2.2.1
    (Row.step_pos (D.shapes row (rowAt_mem hr))) he
  rw [D.copyPoint_old nonempty p e (by omega), D.copyPoint_old nonempty p (r.val + 1) (by omega),
    ← D.source_eq hr he]
  exact D.retainedRow_elementary nonempty r old

theorem retainedRow_copy_critical (nonempty : 0 < a.length) (p : Nat) (r : FiniteRowIndex a)
    (old : r.val < a.length) {row : IBLP.Row} {minimum : Nat}
    (hr : rowAt a r.val = some row) (hm : row.columns.head? = some minimum) :
    (D.lastExtension nonempty).next.model.GraphCriticalPoint (D.retainedRowGraph nonempty r old)
      ((D.lastExtension nonempty).next.ordinal (D.copyPoint nonempty p minimum)) := by
  have member : minimum ∈ row.columns := by
    obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp
      (show row.columns[0]? = some minimum by simpa only [List.head?_eq_getElem?] using hm)
    exact List.mem_iff_getElem.mpr ⟨0, bound, value⟩
  have mb := Row.column_le_last (D.valid _ _ hr) member
  rw [D.copyPoint_old nonempty p minimum (by omega)]
  exact (stage.model.graphCriticalPoint_absolute (D.lastExtension nonempty).next.model
    (D.graph r) (stage.ordinal (D.point minimum)) _ _ rfl rfl).mp (D.critical r row minimum hr hm)

theorem retainedRow_copy_edges (nonempty : 0 < a.length) (p : Nat) (r : FiniteRowIndex a)
    (old : r.val < a.length) {row : IBLP.Row} (hr : rowAt a r.val = some row) :
    ∀ edge ∈ row.edgePairs r.val,
      ZFSet.pair (D.copyPoint nonempty p edge.1).toZFSet (D.copyPoint nonempty p edge.2).toZFSet ∈
        (D.retainedRowGraph nonempty r old).val := by
  intro edge member
  have bounds := Row.edge_index_bounds (D.valid _ _ hr) member
  rw [D.copyPoint_old nonempty p edge.1 (by omega), D.copyPoint_old nonempty p edge.2 (by omega)]
  exact D.edges r row hr edge member

end IBLP.FiniteBoundedData
