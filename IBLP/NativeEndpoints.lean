import IBLP.NativeStrongClosure
import IBLP.ScanTermination
import FullMarkedBLP.NativeBlockEndpoint
import FullMarkedBLP.NativeTopOldEdgeIndices

namespace IBLP.NativeBridge

@[simp] theorem encode_get_e (block : IBLP.Pattern) (j : Nat) :
    ((encode block)[j]?).bind FullMarkedBLP.Row.e = (block[j]?).bind IBLP.Row.e := by
  cases entry : block[j]? <;> simp [encode, List.getElem?_map, entry, Bind.bind, Option.bind]

@[simp] theorem encode_get_p (block : IBLP.Pattern) (j : Nat) :
    ((encode block)[j]?).bind FullMarkedBLP.Row.p = (block[j]?).bind IBLP.Row.p := by
  cases entry : block[j]? <;> simp [encode, List.getElem?_map, entry, Bind.bind, Option.bind]

theorem encoded_block {row : IBLP.Row} {r : Nat} {sources : List Nat} {block : IBLP.Pattern}
    (run : IBLP.nativeBlock row r sources = some block) :
    FullMarkedBLP.nativeBlock (encodeRow row) r sources = some (encode block) := by
  rw [nativeBlock_encode, run]
  rfl

end IBLP.NativeBridge

namespace IBLP

theorem nativeBlock_source_e {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r p e x : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : nativeSources a r = some sources) (member : x ∈ sources)
    (blockRun : nativeBlock row r sources = some block) :
    (block[(sources.filter (· < x)).length]?).bind Row.e = some x := by
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode a) r = some (NativeBridge.encodeRow row) := by simp [hr]
  simpa only [NativeBridge.encode_get_e] using FullMarkedBLP.nativeBlock_source_e
    (NativeBridge.valid_encode valid shapes) encodedRow hp he
    ((NativeBridge.nativeSources_encode a r).trans run) member (NativeBridge.encoded_block blockRun)

theorem nativeBlock_source_p {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r p e x : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : nativeSources a r = some sources) (member : x ∈ sources)
    (blockRun : nativeBlock row r sources = some block) :
    (block[(sources.filter (· < x)).length + 1]?).bind Row.p = some x := by
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode a) r = some (NativeBridge.encodeRow row) := by simp [hr]
  simpa only [NativeBridge.encode_get_p] using FullMarkedBLP.nativeBlock_source_p
    (NativeBridge.valid_encode valid shapes) encodedRow hp he
    ((NativeBridge.nativeSources_encode a r).trans run) member (NativeBridge.encoded_block blockRun)

theorem nativeSources_ascending_rank {a : Pattern} (valid : BasicValid a)
    {r j x : Nat} {sources : List Nat} (run : nativeSources a r = some sources)
    (entry : sources.reverse[j]? = some x) : (sources.filter (· < x)).length = j := by
  have sorted : sources.reverse.Pairwise (· < ·) := (nativeSources_decreasing valid run).reverse
  simpa only [List.filter_reverse, List.length_reverse] using FullMarkedBLP.sorted_rank_at_index sorted entry

theorem nativeBlock_top_e {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r p e : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : nativeSources a r = some sources) (blockRun : nativeBlock row r sources = some block) :
    (block[sources.length]?).bind Row.e = some e := by
  by_cases empty : sources = []
  · subst sources
    have same : block = [row] := (Option.some.inj blockRun).symm
    simpa only [same, List.length_nil, List.getElem?_cons_zero, Option.bind_some] using he
  have encodedValid := NativeBridge.valid_encode valid shapes
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode a) r = some (NativeBridge.encodeRow row) := by simp [hr]
  have encodedSources := (NativeBridge.nativeSources_encode a r).trans run
  have encodedBlock := NativeBridge.encoded_block blockRun
  have len := FullMarkedBLP.nativeBlock_length encodedBlock
  have index := FullMarkedBLP.nativeBlock_actual_e encodedValid encodedRow encodedSources empty encodedBlock
    sources.length (by omega)
  have shape := shapes row (rowAt_mem hr)
  have positive := Row.step_pos shape
  have room := Row.step_lt_length shape
  have endpointAt : row.columns[row.columns.length - row.step]? = some e := by
    simpa only [Row.e, fromRight, show 0 < row.step ∧ row.step ≤ row.columns.length by omega, if_true] using he
  have high := FullMarkedBLP.nativeTop_high_entry encodedValid encodedRow hp he encodedSources endpointAt (Nat.le_refl _)
  have align : row.columns.length - (row.step + 1) + sources.length + 1 = row.columns.length - row.step + sources.length := by omega
  rw [NativeBridge.encode_columns, NativeBridge.encode_step, align, high] at index
  have result : ((NativeBridge.encode block)[sources.length]?).bind FullMarkedBLP.Row.e = some e := by
    simpa only [List.getElem?_eq_getElem (by omega : sources.length < (NativeBridge.encode block).length), Option.bind_some] using index
  simpa only [NativeBridge.encode_get_e] using result

/-- The actual e-entry of every native family row is the ascending record
source assigned to that row, with the old endpoint at the top. -/
theorem nativeBlock_e {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {r p e j : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (run : nativeSources a r = some sources) (blockRun : nativeBlock row r sources = some block)
    (bound : j ≤ sources.length) :
    (block[j]?).bind Row.e = some (if j < sources.length then sources.reverse[j]?.getD 0 else e) := by
  by_cases before : j < sources.length
  · have jb : j < sources.reverse.length := by simpa using before
    have entry : sources.reverse[j]? = some sources.reverse[j] := List.getElem?_eq_getElem jb
    have member := List.mem_reverse.mp (List.getElem_mem jb)
    have rank := nativeSources_ascending_rank valid run entry
    have value := nativeBlock_source_e valid shapes hr hp he run member blockRun
    rw [rank] at value
    simpa only [if_pos before, entry, Option.getD_some] using value
  · have last : j = sources.length := by omega
    subst j
    simpa only [if_neg (Nat.lt_irrefl _)] using nativeBlock_top_e valid shapes hr hp he run blockRun

end IBLP
