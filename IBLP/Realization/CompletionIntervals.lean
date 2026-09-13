import IBLP.CompletionStrongClosure
import IBLP.NativeEdgeBridge

/-! The old-edge insertion intervals follow from the actual bounded map
and the packet equations. No full-rank owner representation is substituted
for a saved bounded graph. -/
namespace IBLP.FiniteBoundedData
universe u
variable {stage : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData stage a)

theorem completion_old_intervals (r : FiniteRowIndex a) {row : Row} {mark : Nat}
    {sources : List Nat} (hr : rowAt a r.val = some row)
    (C : row.CompletionGeometry r.val mark sources)
    (packet : ∀ s ∈ sources, D.nativeImage r s = D.point (mark + 1 + (sources.filter (· < s)).length))
    {k x z p e : Nat} (hp : row.p = some p) (he : row.e = some e)
    (hk : row.step ≤ k) (hz : row.columns[k]? = some z)
    (hx : row.columns[k - row.step]? = some x) :
    (x ≤ z ∧ z ≤ mark ∧ ∀ s ∈ sources, x < s ∧ s < z) ∨
      (x ≤ mark ∧ mark + sources.length < z ∧ ∀ s ∈ sources, s < x) := by
  have valid := D.valid _ _ hr
  have shape := D.shapes row (rowAt_mem hr)
  have old : (NativeBridge.encodeRow row).CoreValid r.val :=
    ⟨valid.1, valid.2.1, valid.2.2.1, NativeBridge.shape_encode shape⟩
  have xp := FullMarkedBLP.step_source_le_p old hz hx hp
  have pz := FullMarkedBLP.target_position_after_p old hk hz hp
  have pm := FullMarkedBLP.target_position_after_p old
    (Nat.le_trans (Nat.le_succ _) C.positive) C.mark_at hp
  have pe := FullMarkedBLP.row_p_lt_e old hp he
  have endpoint := rowEndpoint_eq hr he
  have zb := Row.column_le_last valid (List.mem_of_getElem? hz)
  have rowBound := r.property.2
  have oldEdge : D.nativeImage r x = D.point z := by
    apply D.nativeImage_edges r hr (k - row.step) x z (FullMarkedBLP.full_entry_of_core hx)
    change ((NativeBridge.encodeRow row).full r.val)[k - row.step + row.step]? = some z
    rw [Nat.sub_add_cancel hk]
    exact FullMarkedBLP.full_entry_of_core hz
  have order : ∀ i j, i ≤ e → j ≤ e → D.nativeImage r i < D.nativeImage r j → i < j := by
    intro i j hi hj less
    by_contra hn
    have rev := (D.nativeImage_strictMonoOn r).monotoneOn
      (show j ≤ rowEndpoint a r.val by omega) (show i ≤ rowEndpoint a r.val by omega)
      (Nat.le_of_not_gt hn)
    exact not_lt_of_ge rev less
  by_cases before : z ≤ mark
  · refine Or.inl ⟨by omega, before, ?_⟩
    intro s hs
    have sp := C.sources_below_p valid.1 shape hp s hs
    have rankBound : (sources.filter (· < s)).length < sources.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨s, hs, by simp⟩
    have less : D.nativeImage r x < D.nativeImage r s := by
      rw [oldEdge, packet s hs]
      apply D.point_increasing
      · change z ≤ a.length + 1; omega
      · change mark + 1 + (sources.filter (· < s)).length ≤ a.length + 1
        have := C.before_owner; omega
      · omega
    exact ⟨order x s (by omega) (by omega) less, by omega⟩
  · have high : mark + sources.length < z := by
      by_contra hn
      exact C.target_gap z (by omega) (by omega) (List.mem_of_getElem? hz)
    refine Or.inr ⟨by omega, high, ?_⟩
    intro s hs
    have sp := C.sources_below_p valid.1 shape hp s hs
    have rankBound : (sources.filter (· < s)).length < sources.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨s, hs, by simp⟩
    have less : D.nativeImage r s < D.nativeImage r x := by
      rw [oldEdge, packet s hs]
      apply D.point_increasing
      · change mark + 1 + (sources.filter (· < s)).length ≤ a.length + 1
        have := C.before_owner; omega
      · change z ≤ a.length + 1; omega
      · omega
    exact order s x (by omega) (by omega) less

theorem completion_old_core_pairs (r : FiniteRowIndex a) {row : Row} {mark : Nat}
    {sources : List Nat} (hr : rowAt a r.val = some row)
    (C : row.CompletionGeometry r.val mark sources)
    (packet : ∀ s ∈ sources, D.nativeImage r s = D.point (mark + 1 + (sources.filter (· < s)).length))
    {k x z p e : Nat} (hp : row.p = some p) (he : row.e = some e)
    (hk : row.step ≤ k) (hz : row.columns[k]? = some z)
    (hx : row.columns[k - row.step]? = some x) :
    ∃ j, (completeMarkRow row mark sources).columns[j]? = some x ∧
      (completeMarkRow row mark sources).columns[j + (completeMarkRow row mark sources).step]? = some z := by
  have valid := D.valid _ _ hr
  rcases D.completion_old_intervals r hr C packet hp he hk hz hx with
    ⟨xz, zm, gap⟩ | ⟨xm, high, below⟩
  · obtain ⟨target, source⟩ := FullMarkedBLP.completeMarkRow_earlier_pair
      (row := NativeBridge.encodeRow row) valid.1 C.distinct (C.disjoint valid.1)
      C.target_gap hk hz hx xz zm gap
    simp only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_columns,
      NativeBridge.encode_step] at target source
    refine ⟨k - row.step, ?_, ?_⟩
    · convert source using 1 <;> simp only [completeMarkRow] <;> congr 1 <;> omega
    · convert target using 1 <;> simp only [completeMarkRow] <;> congr 1 <;> omega
  · obtain ⟨target, source⟩ := FullMarkedBLP.completeMarkRow_later_pair
      (row := NativeBridge.encodeRow row) valid.1 C.distinct (C.disjoint valid.1)
      C.target_gap hk hz hx xm below high
    simp only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_columns,
      NativeBridge.encode_step] at target source
    refine ⟨k - row.step + sources.length, ?_, ?_⟩
    · convert source using 1 <;> simp only [completeMarkRow] <;> congr 1 <;> omega
    · convert target using 1 <;> simp only [completeMarkRow] <;> congr 1 <;> omega

end IBLP.FiniteBoundedData
