import IBLP.NativeEndpoints
import FullMarkedBLP.NativeBlockMinimum

namespace IBLP.NativeBridge

/-- Only the already canonical generated row is passed to upstream's
weaker proper-mark interface. No canonicality is imposed on a parent. -/
theorem weak_proper_of_strong {row : FullMarkedBLP.Row} {owner : Nat}
    (valid : row.CoreValid owner) (sorted : row.marks.Pairwise (· < ·))
    (proper : ∀ mark ∈ row.marks, (decodeRow row).ProperMark mark) : row.ProperMarks owner := by
  refine ⟨sorted, ?_⟩
  intro mark member
  have strong := proper mark member
  have below := IBLP.Row.properMark_lt (decoded_basic_of_proper valid proper) strong
  obtain ⟨k, entry, positive, _⟩ := strong
  exact ⟨below, k, by change row.step + 1 ≤ k at positive; omega, entry⟩

theorem top_weak_proper {a : IBLP.Pattern} (valid : IBLP.BasicValid a) (shapes : IBLP.OrdinaryShape a)
    {r : Nat} {row : IBLP.Row} {sources : List Nat} (hr : IBLP.rowAt a r = some row)
    (run : IBLP.nativeSources a r = some sources)
    (proper : ∀ mark ∈ row.marks, row.ProperMark mark) :
    (FullMarkedBLP.nativeTop (encodeRow row) r sources).ProperMarks (r + sources.length) := by
  have encodedRow : FullMarkedBLP.rowAt (encode a) r = some (encodeRow row) := by simp [hr]
  exact weak_proper_of_strong
    (FullMarkedBLP.nativeTop_actual_coreValid (valid_encode valid shapes) encodedRow ((nativeSources_encode a r).trans run))
    (FullMarkedBLP.nativeTop_sorted (encodeRow row) r sources).2 (top_strong_proper valid shapes hr run proper)

end IBLP.NativeBridge

namespace IBLP

theorem nativeBlock_minimum {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r c : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (sourcesRun : nativeSources a r = some sources)
    (proper : ∀ mark ∈ row.marks, row.ProperMark mark) (minimum : row.columns.head? = some c)
    (run : nativeBlock row r sources = some block) : ∀ out ∈ block, out.columns.head? = some c := by
  have encodedValid := NativeBridge.valid_encode valid shapes
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode a) r = some (NativeBridge.encodeRow row) := by simp [hr]
  have encodedSources := (NativeBridge.nativeSources_encode a r).trans sourcesRun
  have encodedBlock := NativeBridge.encoded_block run
  have hv := encodedValid _ _ encodedRow
  cases sources with
  | nil =>
    have same : block = [row] := (Option.some.inj run).symm
    intro out member
    rw [same] at member
    have eq := List.mem_singleton.mp member
    subst out
    exact minimum
  | cons s ss =>
    have nonempty : s :: ss ≠ [] := by simp
    have eligible := FullMarkedBLP.nativeSources_nonempty_eligible encodedRow encodedSources nonempty
    have minStep := FullMarkedBLP.nativeSources_nonempty_step_ge_two hv encodedRow encodedSources nonempty
    change 2 ≤ row.step at minStep
    have topValid := FullMarkedBLP.nativeTop_actual_coreValid encodedValid encodedRow encodedSources
    have topLength := FullMarkedBLP.nativeTop_actual_length encodedValid encodedRow encodedSources
    have targets := FullMarkedBLP.nativeTop_contains_targets hv (s :: ss)
    have topProper := NativeBridge.top_weak_proper valid shapes hr sourcesRun proper
    have topMinimum := FullMarkedBLP.nativeTop_preserves_minimum encodedValid encodedRow encodedSources minimum
    have allMinimum : FullMarkedBLP.BlockMinimum c (NativeBridge.encode block) := by
      by_cases medium : row.columns.length = 2 * row.step
      · obtain ⟨result, computed, resultMinimum⟩ := FullMarkedBLP.nativeBlockDown_medium_minimum ss.length
          topValid topProper topMinimum
          (by change _ = 2 * (row.step + (s :: ss).length); change _ = row.columns.length + 2 * (s :: ss).length at topLength; omega)
          (by change _ ≤ row.step + (s :: ss).length; simp; omega) targets
        have actual : FullMarkedBLP.nativeBlockDown (s :: ss).length (r + (s :: ss).length) true
            (FullMarkedBLP.nativeTop (NativeBridge.encodeRow row) r (s :: ss)) = some (NativeBridge.encode block) := by
          simpa only [FullMarkedBLP.nativeBlock, List.isEmpty_cons, Bool.false_eq_true, if_false,
            NativeBridge.encode_columns, NativeBridge.encode_step, medium, beq_self_eq_true] using encodedBlock
        have same := Option.some.inj (computed.symm.trans actual)
        rwa [same] at resultMinimum
      · have short := FullMarkedBLP.Row.short_shape_of_eligible_ne_medium hv.2.2.2 eligible medium
        change row.columns.length + 1 = 2 * row.step ∧ 3 ≤ row.step at short
        obtain ⟨result, computed, resultMinimum⟩ := FullMarkedBLP.nativeBlockDown_short_minimum (s :: ss).length
          topValid topProper topMinimum
          (by change _ + 1 = 2 * (row.step + (s :: ss).length); change _ = row.columns.length + 2 * (s :: ss).length at topLength; omega)
          (by change _ ≤ row.step + (s :: ss).length; omega) targets
        have notMedium : (row.columns.length == 2 * row.step) = false := by simp [medium]
        have actual : FullMarkedBLP.nativeBlockDown (s :: ss).length (r + (s :: ss).length) false
            (FullMarkedBLP.nativeTop (NativeBridge.encodeRow row) r (s :: ss)) = some (NativeBridge.encode block) := by
          simpa only [FullMarkedBLP.nativeBlock, List.isEmpty_cons, Bool.false_eq_true, if_false,
            NativeBridge.encode_columns, NativeBridge.encode_step, notMedium] using encodedBlock
        have same := Option.some.inj (computed.symm.trans actual)
        rwa [same] at resultMinimum
    intro out member
    obtain ⟨j, jb, value⟩ := List.mem_iff_getElem.mp member
    have encodedBound : j < (NativeBridge.encode block).length := by simpa only [NativeBridge.encode, List.length_map] using jb
    have actual := allMinimum j encodedBound
    simpa only [NativeBridge.encode, List.getElem_map, value, NativeBridge.encode_columns] using actual

end IBLP
