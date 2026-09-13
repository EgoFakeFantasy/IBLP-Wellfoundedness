import IBLP.Realization.CompletionIntervals
import IBLP.Realization.ShiftRowData
import IBLP.Model.WriteOrdinalEdge
import FullMarkedBLP.CompletionEdgeExhaustion

namespace IBLP.FiniteBoundedData
universe u
variable {stage : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData stage a)
variable (r : FiniteRowIndex a) {row : Row} {mark : Nat} {sources : List Nat}
variable (hr : rowAt a r.val = some row) (C : row.CompletionGeometry r.val mark sources)
variable (packet : ∀ s ∈ sources, D.nativeImage r s = D.point (mark + 1 + (sources.filter (· < s)).length))

include hr C packet in
theorem completion_all_edges :
    (NativeBridge.encodeRow (completeMarkRow row mark sources)).RealizesEdges
      (stage.rho (D.map r)) D.point r.val := by
  have valid := D.valid _ _ hr
  have shape := D.shapes row (rowAt_mem hr)
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.columns) (k := row.step + 1)
    (by omega) (by have := Row.step_lt_length shape; omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.columns) (Row.step_pos shape)
    (Row.step_lt_length shape).le
  have old : (NativeBridge.encodeRow row).CoreValid r.val :=
    ⟨valid.1, valid.2.1, valid.2.2.1, NativeBridge.shape_encode shape⟩
  have below : ∀ x ∈ sources, x < e := fun x hx =>
    (C.sources_below_p valid.1 shape hp x hx).trans (FullMarkedBLP.row_p_lt_e old hp he)
  have em := (Row.properMark_above_e valid.1 shape C.proper he).le
  rw [← NativeBridge.completeMarkRow_encode]
  apply FullMarkedBLP.completeMarkRow_edges_of_all_pairs old he em
    (by simpa only [NativeBridge.completeMarkRow_encode] using C.encoded_valid valid shape)
    (by simpa only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_e] using C.preserves_e valid shape he)
    (D.nativeImage_edges r hr) packet
  · intro i x z hx hz
    have sourceAt := (FullMarkedBLP.full_edge_source_bound old he hx hz).1
    change row.columns[i]? = some x at sourceAt
    by_cases inCore : i + row.step < row.columns.length
    · have targetAt : row.columns[i + row.step]? = some z := by
        simpa only [FullMarkedBLP.Row.full, NativeBridge.encode_columns, NativeBridge.encode_step,
          List.getElem?_append_left inCore] using hz
      have pairedAt : row.columns[i + row.step - row.step]? = some x := by simpa using sourceAt
      obtain ⟨j, left, right⟩ := D.completion_old_core_pairs r hr C packet hp he
        (show row.step ≤ i + row.step by omega) targetAt pairedAt
      simp only [NativeBridge.completeMarkRow_encode]
      exact ⟨j, FullMarkedBLP.full_entry_of_core left, FullMarkedBLP.full_entry_of_core right⟩
    · have length := (List.getElem?_eq_some_iff.mp hz).1
      change i + row.step < (row.columns ++ [r.val + 1]).length at length
      simp only [List.length_append, List.length_singleton] at length
      have index : i + row.step = row.columns.length := by omega
      have sourceIndex : i = row.columns.length - row.step := by omega
      have atE : row.columns[row.columns.length - row.step]? = some e := by
        simpa only [Row.e, fromRight, show 0 < row.step ∧ row.step ≤ row.columns.length from
          ⟨Row.step_pos shape, (Row.step_lt_length shape).le⟩, if_true] using he
      have xe : x = e := by rw [sourceIndex, atE] at sourceAt; exact (Option.some.inj sourceAt).symm
      have zend : z = r.val + 1 := by
        change (row.columns ++ [r.val + 1])[i + row.step]? = some z at hz
        simpa only [index, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] using hz.symm
      rw [xe, zend]
      exact FullMarkedBLP.completeMarkRow_endpoint_pair old he em C.distinct
        (C.disjoint valid.1) C.target_gap below
  · intro x hx
    obtain ⟨j, bound, targetAt, sourceAt⟩ := FullMarkedBLP.completeMarkRow_new_pair
      (row := NativeBridge.encodeRow row) valid.1 C.distinct
      (Nat.le_trans (Nat.le_succ _) C.positive) C.mark_at C.left_at C.right_at C.source_gap
      (C.sources_below_mark valid.1 shape) C.target_gap hx
    refine ⟨j - (FullMarkedBLP.completeMarkRow (NativeBridge.encodeRow row) mark sources).step,
      FullMarkedBLP.full_entry_of_core sourceAt, ?_⟩
    rw [Nat.sub_add_cancel bound]
    convert FullMarkedBLP.full_entry_of_core (owner := r.val) targetAt using 1 <;> congr 1 <;> omega

include hr C packet in
theorem completion_graph_edge {edge : Nat × Nat}
    (member : edge ∈ (completeMarkRow row mark sources).edgePairs r.val) :
    ZFSet.pair (D.point edge.1).toZFSet (D.point edge.2).toZFSet ∈ (D.graph r).val := by
  have valid := D.valid _ _ hr
  have shape := D.shapes row (rowAt_mem hr)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.columns) (Row.step_pos shape) (Row.step_lt_length shape).le
  obtain ⟨k, left, right⟩ := Row.edgePairs_iff.mp member
  have sourceBound := (FullMarkedBLP.full_edge_source_bound (C.encoded_valid valid shape)
    (C.preserves_e valid shape he) left right).2
  have endpointBound := Row.column_le_last valid (fromRight_mem he)
  have pointBound : D.point edge.1 ≤ D.source r.val := by
    rw [D.source_eq hr he]
    exact D.point_increasing.monotoneOn
      (by change edge.1 ≤ a.length + 1; have := r.property.2; omega)
      (by change e ≤ a.length + 1; have := r.property.2; omega) sourceBound
  exact (D.graph_represents r).write_ordinal_edge pointBound
    (D.completion_all_edges r hr C packet k edge.1 edge.2 left right)

/-- Completion retains exactly the old saved graph, with its actual
source endpoint, critical minimum and every new and old full-row edge. -/
noncomputable def completionRowData : RowGraphData stage D.point r.val (completeMarkRow row mark sources) where
  graph := D.graph r
  elementary := by
    intro e he
    have shape := D.shapes row (rowAt_mem hr)
    obtain ⟨oldE, oldAt⟩ := fromRight_exists (xs := row.columns) (Row.step_pos shape) (Row.step_lt_length shape).le
    have retained := C.preserves_e (D.valid _ _ hr) shape oldAt
    have same := Option.some.inj (he.symm.trans retained)
    rw [same]
    exact (D.savedRowData r hr).elementary oldE oldAt
  critical := by
    intro minimum hm
    have size := (D.valid _ _ hr).2.1
    have oldAt : row.columns.head? = some (row.columns[0]'(by omega)) := by
      simpa only [List.head?_eq_getElem?] using (List.getElem?_eq_getElem (by omega : 0 < row.columns.length))
    have retained := C.preserves_minimum (D.valid _ _ hr) (D.shapes row (rowAt_mem hr)) oldAt
    have same := Option.some.inj (hm.symm.trans retained)
    rw [same]
    exact D.critical r row _ hr oldAt
  edges := fun _ member => D.completion_graph_edge r hr C packet member

theorem completionRowData_graph : (D.completionRowData r hr C packet).graph = D.graph r := rfl

end IBLP.FiniteBoundedData
