import IBLP.CompletionOldPairs
import IBLP.CompletionTrace

namespace IBLP

theorem markTrace_pair_data {a : Pattern} {r mark : Nat} {rows : List Nat}
    (computed : markTrace a r mark = some rows) :
    ∃ row k source, rowAt a r = some row ∧ row.step ≤ k ∧
      row.columns[k]? = some mark ∧ row.columns[k - row.step]? = some source ∧
      Trace a source mark rows := by
  unfold markTrace at computed
  obtain ⟨row, atRow, computed⟩ := Option.bind_eq_some_iff.mp computed
  split at computed
  · rename_i member
    dsimp only at computed
    split at computed
    · rename_i legal
      obtain ⟨source, atSource, trace⟩ := Option.bind_eq_some_iff.mp computed
      exact ⟨row, row.columns.idxOf mark, source, atRow, legal,
        List.getElem?_idxOf member, atSource, traceFrom_iff.mp trace⟩
    · simp at computed
  · simp at computed

theorem markTrace_of_pair {a : Pattern} {r mark k source : Nat} {row : Row} {rows : List Nat}
    (atRow : rowAt a r = some row) (sorted : row.columns.Pairwise (· < ·))
    (legal : row.step ≤ k) (atMark : row.columns[k]? = some mark)
    (atSource : row.columns[k - row.step]? = some source) (trace : Trace a source mark rows) :
    markTrace a r mark = some rows := by
  have index := sorted_idxOf_of_at sorted atMark
  have member := List.mem_of_getElem? atMark
  simp [markTrace, atRow, member, index, legal, atSource, traceFrom_iff.mpr trace]

/-- A local geometric completion retains every previously successful
computed mark trace, including its terminal paired source. -/
theorem Row.CompletionGeometry.set_markTrace {a : Pattern} (valid : IBLP.BasicValid a)
    (shapes : IBLP.OrdinaryShape a) {owner mark : Nat} {row : Row} {sources : List Nat}
    (atRow : rowAt a owner = some row) (C : row.CompletionGeometry owner mark sources)
    {r z : Nat} {rows : List Nat} (computed : markTrace a r z = some rows) :
    markTrace (a.set (owner - 1) (completeMarkRow row mark sources)) r z = some rows := by
  obtain ⟨old, k, source, atOld, legal, atTarget, atSource, trace⟩ := markTrace_pair_data computed
  have newTrace := trace.completion atRow (valid _ _ atRow) (shapes row (rowAt_mem atRow)) C
  by_cases same : r = owner
  · subst r
    have equal : old = row := Option.some.inj (atOld.symm.trans atRow)
    subst old
    obtain ⟨j, sourceAt, targetAt⟩ := C.old_core_pairs (valid _ _ atRow)
      (shapes row (rowAt_mem atRow)) legal atTarget atSource
    exact markTrace_of_pair (rowAt_set_self atRow)
      (C.encoded_valid (valid _ _ atRow) (shapes row (rowAt_mem atRow))).1
      (by omega) targetAt (by simpa only [Nat.add_sub_cancel_right] using sourceAt) newTrace
  · exact markTrace_of_pair ((rowAt_set_other atRow same).trans atOld)
      (valid _ _ atOld).1 legal atTarget atSource newTrace

end IBLP
