import IBLP.Realization.NativeMarkPayload

namespace IBLP.MarkedRealization
open FullMarkedBLP
universe u
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
  (sourcesRun : IBLP.nativeSources a r.val = some sources)
  {b : IBLP.Pattern} (run : IBLP.native a r.val = some (b, sources))

theorem native_parent_markPairs :
    NativeBridge.MarkPairs (R.data.nativeMarkPayload r hr hp he sourcesRun R.proper run) (NativeBridge.encodeRow row) := by
  intro mark member
  obtain ⟨source, trace, paired, _, factors, certificate⟩ := R.marks r.val row mark hr member
  have proper := R.proper row (rowAt_mem hr) mark member
  have indices := IBLP.Row.properMark_indices (R.data.valid _ _ hr) proper
  have before := IBLP.Row.properMark_lt (R.data.valid _ _ hr) proper
  exact ⟨row.columns.idxOf mark, source, by change row.step ≤ row.columns.idxOf mark; omega,
    List.getElem?_idxOf indices.1, paired,
    R.data.nativeMarkPayload_old r hr hp he sourcesRun R.proper run factors before certificate⟩

theorem native_top_markPairs :
    NativeBridge.MarkPairs (R.data.nativeMarkPayload r hr hp he sourcesRun R.proper run)
      (FullMarkedBLP.nativeTop (NativeBridge.encodeRow row) r.val sources) :=
  NativeBridge.top_markPairs _ R.data.valid R.data.shapes hr hp sourcesRun run
    (R.proper row (rowAt_mem hr)) (R.native_parent_markPairs r hr hp he sourcesRun run)
    (R.data.nativeMarkPayload_direct r hr hp he sourcesRun R.proper run)

/-- Every actual mark on every generated family row has its literal paired
source, algorithmic trace, and complete weak certificate. The same proof
covers inherited marks and newly introduced direct marks. -/
theorem native_family_markRealized {block : IBLP.Pattern} {out : IBLP.Row} {j mark : Nat}
    (blockRun : IBLP.nativeBlock row r.val sources = some block) (entry : block[j]? = some out)
    (marked : mark ∈ out.marks) :
    (R.data.nativeData r hr hp he sourcesRun R.proper run).MarkRealized (r.val + j) out mark := by
  let E := R.data.nativeData r hr hp he sourcesRun R.proper run
  have length := IBLP.nativeBlock_length blockRun
  have jb := (List.getElem?_eq_some_iff.mp entry).1
  have atOut : IBLP.rowAt b (r.val + j) = some out :=
    (IBLP.native_family_rowAt hr run blockRun jb).trans entry
  have outValid := E.valid _ _ atOut
  have outProper := IBLP.nativeBlock_proper R.data.valid R.data.shapes hr sourcesRun
    (R.proper row (rowAt_mem hr)) blockRun out (List.mem_of_getElem? entry) mark marked
  have before := IBLP.Row.properMark_lt outValid outProper
  have pairs := IBLP.nativeBlock_markPairs (R.data.nativeMarkPayload r hr hp he sourcesRun R.proper run)
    R.data.valid R.data.shapes hr sourcesRun (R.proper row (rowAt_mem hr)) blockRun
    (R.native_parent_markPairs r hr hp he sourcesRun run) (R.native_top_markPairs r hr hp he sourcesRun run)
    out (List.mem_of_getElem? entry) mark marked
  obtain ⟨k, source, index, targetAt, sourceAt, payload⟩ := pairs
  obtain ⟨rows, history, agreement⟩ := payload
  have idx : out.columns.idxOf mark = k := IBLP.sorted_idxOf_of_at outValid.1 targetAt
  have paired : out.columns[out.columns.idxOf mark - out.step]? = some source := by rw [idx]; exact sourceAt
  have column : mark ∈ out.columns := List.mem_of_getElem? targetAt
  have legal : out.step ≤ out.columns.idxOf mark := by rw [idx]; exact index
  have computed : IBLP.markTrace b (r.val + j) mark = some (rows ++ [source]) := by
    simp [IBLP.markTrace, atOut, column, legal, paired, traceFrom_iff.mpr history.toTrace]
  let i : FiniteRowIndex b := ⟨r.val + j, rowAt_pos atOut, rowAt_le_length atOut⟩
  have certificate := R.data.nativeMarkPayload_certificate r hr hp he sourcesRun R.proper run history agreement i
    (by change r.val ≤ r.val + j; omega) (by change r.val + j ≤ r.val + sources.length; omega) before
  refine ⟨source, rows ++ [source], paired, computed, ?_⟩
  simp only [List.dropLast_concat]
  exact ⟨history, certificate⟩

end IBLP.MarkedRealization
