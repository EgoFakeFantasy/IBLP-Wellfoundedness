import IBLP.NativeEdgeBridge
import FullMarkedBLP.NativeTopEdges

/-! The literal index case split follows the fixed upstream native top
edge proof (Apache-2.0). Here the action is read from an actual internal
saved graph, and every new point is the original IBLP construction. -/
namespace IBLP.FiniteBoundedData
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)

theorem nativeTop_edges (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
    (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : IBLP.nativeSources a r.val = some sources) (nonempty : sources ≠ []) :
    (NativeBridge.encodeRow (IBLP.nativeTop row r.val sources)).RealizesEdges
      (stage.rho (D.map r)) (D.nativePoint r sources) (r.val + sources.length) := by
  rw [← NativeBridge.nativeTop_encode]
  have valid := NativeBridge.valid_encode D.valid D.shapes
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode a) r.val = some (NativeBridge.encodeRow row) := by simp [hr]
  have encodedSources := (NativeBridge.nativeSources_encode a r.val).trans run
  have hv := valid _ _ encodedRow
  have room := FullMarkedBLP.Row.step_lt_length hv.2.2.2
  change row.step < row.columns.length at room
  intro k x y hx hy
  rcases FullMarkedBLP.nativeTop_edge_source_cases valid encodedRow encodedSources hy with low | ⟨z, member, index⟩ | last
  · change k < row.columns.length - row.step at low
    have kb : k < row.columns.length := by omega
    have kt : k + row.step < row.columns.length := by omega
    have left : row.columns[k]? = some row.columns[k] := List.getElem?_eq_getElem kb
    have right : row.columns[k + row.step]? = some row.columns[k + row.step] := List.getElem?_eq_getElem kt
    obtain ⟨newLeft, newRight⟩ := FullMarkedBLP.nativeTop_all_old_core_pair_indices valid encodedRow hp he
      encodedSources nonempty left right
    have ex : x = row.columns[k] := Option.some.inj (hx.symm.trans (FullMarkedBLP.full_entry_of_core newLeft))
    have ey : y = row.columns[k + row.step] := Option.some.inj (hy.symm.trans (FullMarkedBLP.full_entry_of_core newRight))
    subst x; subst y
    rw [D.nativePoint_before r sources (IBLP.Row.column_le_last (D.valid _ _ hr) (List.mem_of_getElem? left)),
      D.nativePoint_before r sources (IBLP.Row.column_le_last (D.valid _ _ hr) (List.mem_of_getElem? right))]
    exact D.nativeImage_edges r hr k _ _ (FullMarkedBLP.full_entry_of_core left) (FullMarkedBLP.full_entry_of_core right)
  · obtain ⟨left, right⟩ := FullMarkedBLP.nativeTop_inserted_pair_indices valid encodedRow hp he encodedSources member
    rw [index] at hx hy
    have ex : x = z := Option.some.inj (hx.symm.trans (FullMarkedBLP.full_entry_of_core left))
    have ey : y = r.val + 1 + (sources.filter (· < z)).length :=
      Option.some.inj (hy.symm.trans (FullMarkedBLP.full_entry_of_core right))
    subst x; subst y
    have below := FullMarkedBLP.nativeSources_below_owner valid encodedRow encodedSources z member
    have rankBound : (sources.filter (· < z)).length < sources.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨z, member, by simp⟩
    rw [D.nativePoint_before r sources below.le, D.nativePoint_inserted r sources _ rankBound,
      D.nativeFresh_source_rank r run member]
    rfl
  · have positive := IBLP.Row.step_pos (D.shapes row (IBLP.rowAt_mem hr))
    have endpointAt : row.columns[row.columns.length - row.step]? = some e := by
      simpa only [IBLP.Row.e, IBLP.fromRight, show 0 < row.step ∧ row.step ≤ row.columns.length by omega, if_true] using he
    have newEndpoint := FullMarkedBLP.nativeTop_high_entry valid encodedRow hp he encodedSources endpointAt (Nat.le_refl _)
    rw [last] at hx hy
    have ex : x = e := Option.some.inj (hx.symm.trans (FullMarkedBLP.full_entry_of_core newEndpoint))
    have length := FullMarkedBLP.nativeTop_actual_length valid encodedRow encodedSources
    change _ = row.columns.length + 2 * sources.length at length
    have align : (NativeBridge.encodeRow row).core.length - (NativeBridge.encodeRow row).step + sources.length +
        (FullMarkedBLP.nativeTop (NativeBridge.encodeRow row) r.val sources).step =
        (FullMarkedBLP.nativeTop (NativeBridge.encodeRow row) r.val sources).core.length := by
      change row.columns.length - row.step + sources.length + (row.step + sources.length) = _
      omega
    rw [align] at hy
    have ey : y = r.val + sources.length + 1 := by simpa [FullMarkedBLP.Row.full] using hy.symm
    subst x; subst y
    have eBelow := IBLP.Row.column_le_last (D.valid _ _ hr) (IBLP.fromRight_mem he)
    rw [D.nativePoint_before r sources eBelow]
    have value := D.nativeDomain_image r sources sources.length (Nat.le_refl _)
    simpa only [nativeDomainIndex, if_neg (Nat.lt_irrefl _), rowEndpoint_eq hr he] using value

end IBLP.FiniteBoundedData
