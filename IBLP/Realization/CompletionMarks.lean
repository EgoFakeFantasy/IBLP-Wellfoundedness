import IBLP.Realization.CompletionCertificate
import IBLP.Realization.MarkedRealization

namespace IBLP
universe u

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData stage a)

theorem markRealized_of_pair (r : Nat) {row : Row} (hr : rowAt a r = some row)
    {mark source index : Nat} (legal : row.step ≤ index) (atMark : row.columns[index]? = some mark)
    (atSource : row.columns[index - row.step]? = some source) {rows : List Nat}
    (h : FactorTrace a source mark rows) (certificate : h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r) :
    D.MarkRealized r row mark := by
  have idx := sorted_idxOf_of_at (D.valid _ _ hr).1 atMark
  have paired : row.columns[row.columns.idxOf mark - row.step]? = some source := by rw [idx]; exact atSource
  have member := List.mem_of_getElem? atMark
  have indexBound : row.step ≤ row.columns.idxOf mark := by omega
  refine ⟨source, rows ++ [source], paired, ?_, ?_⟩
  · simp [markTrace, hr, member, indexBound, paired, traceFrom_iff.mpr h.toTrace]
  · simp only [List.dropLast_concat]
    exact ⟨h, certificate⟩

/-- The historical packet obligation of section 6.4 and 7.3: every source
has its accurate parallel chain and the full weak certificate. It is not
asserted to follow from internalCheck alone. -/
def CompletionHistoryPacket (r mark : Nat) (sources : List Nat) : Prop :=
  ∀ s ∈ sources, ∃ rows, ∃ h : FactorTrace a s (mark + 1 + (sources.filter (· < s)).length) rows,
    h.MarkCertificate D.toFiniteTraceRows.toInternalTraceRows r

theorem CompletionHistoryPacket.edge {r : FiniteRowIndex a} {mark : Nat} {sources : List Nat}
    (H : D.CompletionHistoryPacket r.val mark sources) :
    ∀ s ∈ sources, D.nativeImage r s = D.point (mark + 1 + (sources.filter (· < s)).length) := by
  intro s hs
  obtain ⟨rows, h, certificate⟩ := H s hs
  have edge := h.markCertificate_rho_edge D.toFiniteTraceRows.toInternalTraceRows certificate
  change (D.toFiniteTraceRows.toInternalTraceRows.actions.action r.val).rho (D.point s) = _ at edge
  rw [D.toFiniteTraceRows.action_valid r] at edge
  exact edge

end FiniteBoundedData

namespace MarkedRealization
variable {stage : ModelStage.{u}} {a : Pattern} (R : MarkedRealization stage a)
variable (r : FiniteRowIndex a) {row : Row} {mark : Nat} {sources : List Nat}
variable (hr : rowAt a r.val = some row) (C : row.CompletionGeometry r.val mark sources)
variable (packet : ∀ s ∈ sources, R.data.nativeImage r s = R.data.point (mark + 1 + (sources.filter (· < s)).length))

theorem completion_other_markRealized {i z : Nat} {out : Row}
    (atOld : rowAt a i = some out) (other : i ≠ r.val) (marked : z ∈ out.marks) :
    (R.data.completionData r hr C (R.proper row (rowAt_mem hr)) packet).MarkRealized i out z := by
  let E := R.data.completionData r hr C (R.proper row (rowAt_mem hr)) packet
  obtain ⟨source, trace, paired, _, h, certificate⟩ := R.marks i out z atOld marked
  have indices := Row.properMark_indices (R.data.valid _ _ atOld) (R.proper out (rowAt_mem atOld) z marked)
  have atNew := (rowAt_set_other (new := completeMarkRow row mark sources) hr other).trans atOld
  let oldIndex : FiniteRowIndex a := ⟨i, rowAt_pos atOld, rowAt_le_length atOld⟩
  let newIndex : FiniteRowIndex (a.set (r.val - 1) (completeMarkRow row mark sources)) :=
    ⟨i, rowAt_pos atNew, rowAt_le_length atNew⟩
  apply E.markRealized_of_pair i atNew (show out.step ≤ out.columns.idxOf z by omega)
    (List.getElem?_idxOf indices.1) paired
    (h.completion hr (R.data.valid _ _ hr) (R.data.shapes row (rowAt_mem hr)) C)
  exact (R.data.completion_markCertificate r hr C (R.proper row (rowAt_mem hr)) packet
    oldIndex newIndex rfl h).mp certificate

theorem completion_old_markRealized {z : Nat} (marked : z ∈ row.marks) :
    (R.data.completionData r hr C (R.proper row (rowAt_mem hr)) packet).MarkRealized r.val
      (completeMarkRow row mark sources) z := by
  let E := R.data.completionData r hr C (R.proper row (rowAt_mem hr)) packet
  have valid := R.data.valid _ _ hr
  have shape := R.data.shapes row (rowAt_mem hr)
  obtain ⟨source, trace, paired, _, h, certificate⟩ := R.marks r.val row z hr marked
  have indices := Row.properMark_indices valid (R.proper row (rowAt_mem hr) z marked)
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.columns) (k := row.step + 1)
    (by omega) (by have := Row.step_lt_length shape; omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.columns) (Row.step_pos shape) (Row.step_lt_length shape).le
  obtain ⟨j, sourceAt, targetAt⟩ := R.data.completion_old_core_pairs r hr C packet hp he
    (show row.step ≤ row.columns.idxOf z by omega) (List.getElem?_idxOf indices.1) paired
  have atNew := rowAt_set_self (new := completeMarkRow row mark sources) hr
  let newIndex : FiniteRowIndex (a.set (r.val - 1) (completeMarkRow row mark sources)) :=
    ⟨r.val, r.property.1, by simpa only [List.length_set] using r.property.2⟩
  apply E.markRealized_of_pair r.val atNew (show (completeMarkRow row mark sources).step ≤
      j + (completeMarkRow row mark sources).step by omega) targetAt
    (by simpa only [Nat.add_sub_cancel_right] using sourceAt)
    (h.completion hr valid shape C)
  exact (R.data.completion_markCertificate r hr C (R.proper row (rowAt_mem hr)) packet
    r newIndex rfl h).mp certificate

theorem completion_new_markRealized (H : R.data.CompletionHistoryPacket r.val mark sources)
    {s : Nat} (member : s ∈ sources) :
    (R.data.completionData r hr C (R.proper row (rowAt_mem hr)) packet).MarkRealized r.val
      (completeMarkRow row mark sources) (mark + 1 + (sources.filter (· < s)).length) := by
  let E := R.data.completionData r hr C (R.proper row (rowAt_mem hr)) packet
  have valid := R.data.valid _ _ hr
  have shape := R.data.shapes row (rowAt_mem hr)
  obtain ⟨rows, h, certificate⟩ := H s member
  obtain ⟨j, bound, targetAt, sourceAt⟩ := FullMarkedBLP.completeMarkRow_new_pair
    (row := NativeBridge.encodeRow row) valid.1 C.distinct
    (Nat.le_trans (Nat.le_succ _) C.positive) C.mark_at C.left_at C.right_at C.source_gap
    (C.sources_below_mark valid.1 shape) C.target_gap member
  simp only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_columns, NativeBridge.encode_step] at bound targetAt sourceAt
  have targetAt' : (completeMarkRow row mark sources).columns[j]? =
      some (mark + 1 + (sources.filter (· < s)).length) := by
    convert targetAt using 1 <;> congr 1 <;> omega
  let newIndex : FiniteRowIndex (a.set (r.val - 1) (completeMarkRow row mark sources)) :=
    ⟨r.val, r.property.1, by simpa only [List.length_set] using r.property.2⟩
  apply E.markRealized_of_pair r.val (rowAt_set_self hr) bound targetAt' sourceAt
    (h.completion hr valid shape C)
  exact (R.data.completion_markCertificate r hr C (R.proper row (rowAt_mem hr)) packet
    r newIndex rfl h).mp certificate

end MarkedRealization
end IBLP
