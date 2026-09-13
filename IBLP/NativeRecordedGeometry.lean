import IBLP.NativeTraceShift
import IBLP.NativeWalk
import FullMarkedBLP.NativeActualTargetBChain
import FullMarkedBLP.ScanPrefix

namespace IBLP

theorem native_source_predecessor {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r s : Nat} {sources : List Nat} (run : native a r = some (b, sources)) (member : s ∈ sources) :
    predecessor b (r + ((sources.filter (· < s)).length + 1)) = some s := by
  have value := FullMarkedBLP.native_source_predecessor (NativeBridge.valid_encode valid shapes)
    (NativeBridge.encoded_native run) member
  simpa only [NativeBridge.predecessor_encode] using value

/-- The literal q-chain of every positive native family position. -/
theorem native_target_q {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r j : Nat} {sources : List Nat} (run : native a r = some (b, sources))
    (positive : 0 < j) (bound : j ≤ sources.length) : penultimate b (r + j) = some (r + j - 1) := by
  obtain ⟨row, block, hr, sourceRun, blockRun, _⟩ := native_decomposition run
  have nonempty : sources ≠ [] := by intro empty; simp only [empty, List.length_nil] at bound; omega
  have length := nativeBlock_length blockRun
  have index : j < block.length := by omega
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode a) r = some (NativeBridge.encodeRow row) :=
    by simp only [NativeBridge.rowAt_encode, hr, Option.map_some]
  have encodedBlock := NativeBridge.encoded_block blockRun
  have encodedIndex : j < (NativeBridge.encode block).length := by simpa only [NativeBridge.encode, List.length_map] using index
  have value := FullMarkedBLP.nativeBlock_actual_target_b (NativeBridge.valid_encode valid shapes)
    encodedRow ((NativeBridge.nativeSources_encode a r).trans sourceRun) nonempty encodedBlock j encodedIndex positive
  have qValue : (block[j]).q = some (r + j - 1) := by
    simpa only [NativeBridge.encode, List.getElem_map, NativeBridge.encode_q] using value
  simp only [penultimate, native_family_rowAt hr run blockRun index,
    List.getElem?_eq_getElem index, Option.bind_some, qValue]

theorem native_record_source_bounds {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r : Nat} {sources : List Nat} (run : native a r = some (b, sources)) :
    sources.Pairwise (· > ·) ∧ ∀ s ∈ sources, 0 < s ∧ s < r := by
  obtain ⟨row, _, hr, sourceRun, _, _⟩ := native_decomposition run
  have shape := shapes row (rowAt_mem hr)
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.columns) (k := row.step + 1)
    (by omega) (by have := Row.step_lt_length shape; omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.columns) (Row.step_pos shape) (Row.step_lt_length shape).le
  have endpoint := fromRight_le_last (valid _ _ hr).1 (valid _ _ hr).2.2.1 (Row.step_pos shape) he
  refine ⟨nativeSources_decreasing valid sourceRun, ?_⟩
  intro s member
  have bounds := nativeSources_bounds valid hr hp he sourceRun s member
  omega

end IBLP
