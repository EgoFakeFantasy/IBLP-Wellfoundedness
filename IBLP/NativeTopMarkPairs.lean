import IBLP.NativeMarkPairs
import IBLP.NativeTraceShift

namespace IBLP.NativeBridge

/-- Each inherited marked pair has the same source in the top. Each new
marked target has exactly its actual p-source in the output. -/
theorem top_markPairs (P : Nat → Nat → Prop) {a b : IBLP.Pattern}
    (valid : IBLP.BasicValid a) (shapes : IBLP.OrdinaryShape a)
    {r p : Nat} {row : IBLP.Row} {sources : List Nat}
    (hr : IBLP.rowAt a r = some row) (hp : row.p = some p)
    (sourcesRun : IBLP.nativeSources a r = some sources) (run : IBLP.native a r = some (b, sources))
    (proper : ∀ mark ∈ row.marks, row.ProperMark mark) (oldData : MarkPairs P (encodeRow row))
    (direct : ∀ j, j < sources.length → ∃ source, IBLP.predecessor b (r + j) = some source ∧ P (r + j) source) :
    MarkPairs P (FullMarkedBLP.nativeTop (encodeRow row) r sources) := by
  have encodedValid := valid_encode valid shapes
  have encodedRow : FullMarkedBLP.rowAt (encode a) r = some (encodeRow row) := by simp [hr]
  have encodedSources := (nativeSources_encode a r).trans sourcesRun
  have hv := encodedValid _ _ encodedRow
  have room := FullMarkedBLP.Row.step_lt_length hv.2.2.2
  change row.step < row.columns.length at room
  intro mark member
  have origin := member
  simp only [FullMarkedBLP.nativeTop, FullMarkedBLP.mem_canonicalColumns, List.mem_filter,
    List.mem_append, List.mem_map, List.mem_range] at origin
  rcases origin.1 with old | ⟨j, bound, value⟩
  · obtain ⟨k, source, index, targetAt, sourceAt, payload⟩ := oldData mark old
    have below := IBLP.Row.properMark_lt (valid _ _ hr) (proper mark old)
    have sourcesBelow := sources_before_strong_mark valid shapes hr sourcesRun (proper mark old)
    have filtered : sources.filter (· < mark) = sources := by
      apply List.filter_eq_self.mpr
      intro x hx
      simpa only [decide_eq_true_eq] using sourcesBelow x hx
    have rank := FullMarkedBLP.nativeTop_rank_exact encodedValid encodedRow encodedSources below.le
    rw [filtered, FullMarkedBLP.sorted_rank_at_index hv.1 targetAt] at rank
    have inTop := FullMarkedBLP.nativeTop_preserves_entries (encodeRow row) r sources mark (List.mem_of_getElem? targetAt)
    have newTarget := FullMarkedBLP.sorted_get_at_rank (FullMarkedBLP.nativeTop_sorted (encodeRow row) r sources).1 inTop
    rw [rank] at newTarget
    have sourceLe := FullMarkedBLP.step_source_le_p hv targetAt sourceAt hp
    have newSource := FullMarkedBLP.nativeTop_low_entry encodedValid encodedRow hp encodedSources sourceAt sourceLe
    refine ⟨k + sources.length, source, ?_, newTarget, ?_, payload⟩
    · change row.step + sources.length ≤ k + sources.length
      change row.step ≤ k at index
      omega
    · have align : k + sources.length - (FullMarkedBLP.nativeTop (encodeRow row) r sources).step = k - row.step := by
        change k + sources.length - (row.step + sources.length) = k - row.step
        omega
      rw [align]
      exact newSource
  · have same : r + j = mark := value
    subst mark
    obtain ⟨source, pred, payload⟩ := direct j bound
    have nonempty : sources ≠ [] := by intro empty; simp [empty] at bound
    have read := FullMarkedBLP.native_target_predecessor encodedValid encodedRow (encoded_native run) nonempty bound.le
    rw [predecessor_encode, pred] at read
    have target := FullMarkedBLP.nativeTop_target_entry encodedValid encodedRow encodedSources bound.le
    refine ⟨row.columns.length - 1 + sources.length + j, source, ?_, target, ?_, payload⟩
    · change row.step + sources.length ≤ row.columns.length - 1 + sources.length + j
      omega
    · have align : row.columns.length - 1 + sources.length + j -
          (FullMarkedBLP.nativeTop (encodeRow row) r sources).step = row.columns.length - (row.step + 1) + j := by
        change row.columns.length - 1 + sources.length + j - (row.step + sources.length) = _
        omega
      rw [align]
      exact read.symm

end IBLP.NativeBridge
