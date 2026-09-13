import IBLP.Realization.CopyScanQ
import IBLP.Realization.FiniteBlockSaturation
import IBLP.RecordInheritance

namespace IBLP.BoundedRealization
universe u

/-- Actual copied-block record inheritance from conditional entrance
saturation and strictly earlier seed histories. The current owner may use
its already completed frozen geometry, but no current native conclusion.
The seed histories are the remaining well-founded induction obligation. -/
theorem copies_scan_record_inherits {stage : ModelStage.{u}} {a copied initial current result : Pattern}
    (R : BoundedRealization stage a) {last row : Row} {p m k oldCursor v e : Nat}
    {rec : Records} {names : Nat → Nat} {sources : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) (within : k < m)
    (upper : oldCursor < a.length + (k + 1) * (a.length - p))
    (vInBlock : a.length + k * (a.length - p) ≤ v)
    (atOriginal : rowAt initial oldCursor = some row) (originalP : row.p = some v) (originalE : row.e = some e)
    (reach : ScanLabeledReach initial a.length current rec oldCursor names)
    (earlierRows : ScanPriorGeometry initial a.length (names oldCursor))
    (ownerGeometry : FrozenGeometryBefore current rec (names oldCursor) 0)
    (earlierSeeds : ∀ j, a.length + k * (a.length - p) ≤ j →
      j < a.length + (k + 1) * (a.length - p) → j < oldCursor →
      ∀ before records birthNames,
      ScanLabeledReach initial a.length before records j birthNames → birthNames j < names oldCursor →
      SeedRecordHistory initial (a.length + k * (a.length - p))
        (a.length + (k + 1) * (a.length - p)) records birthNames)
    (run : native (completeFrozenMarks current rec (names oldCursor)) (names oldCursor) = some (result, sources))
    (nonempty : sources ≠ []) :
    ∃ saved, (names v, saved) ∈ rec ∧ sources = descendingPacket (names v) saved.length ∧
      blockSeed initial (a.length + k * (a.length - p)) oldCursor =
        blockSeed initial (a.length + k * (a.length - p)) v := by
  obtain ⟨next, _, copiedRealization, _, _⟩ := R.toMarkedRealization.rawCopies_realization_exists m copies
  obtain ⟨entry, _, _⟩ := copiedRealization.cut_realization_exists cut
  have entranceSyntax := reach.forget.syntax_of_geometry entry.data.valid entry.data.shapes entry.proper earlierRows
  have marked := completeFrozenMarks_invariant entranceSyntax.1 entranceSyntax.2.1 entranceSyntax.2.2 ownerGeometry
  have atBefore := reach.unprocessed_rowAt (Nat.le_refl _) atOriginal
  have beforeP : predecessor current (names oldCursor) = some (names v) := by
    simp only [predecessor, atBefore, Option.bind_some]
    change fromRight (row.columns.map names) (row.step + 1) = _
    rw [fromRight_map]
    change row.p.map names = _
    rw [originalP]
    rfl
  have beforeE : (rowAt current (names oldCursor)).bind Row.e = some (names e) := by
    rw [atBefore]
    change fromRight (row.columns.map names) row.step = _
    rw [fromRight_map]
    change row.e.map names = _
    rw [originalE]
    rfl
  obtain ⟨input, block, atInput, sourceRun, _, _⟩ := native_decomposition run
  have inputP : input.p = some (names v) := by
    have h := (marked.predecessors (names oldCursor)).trans beforeP
    simpa only [predecessor, atInput, Option.bind_some] using h
  have inputE : input.e = some (names e) := by
    have h := (marked.endpoints (names oldCursor)).trans beforeE
    simpa only [atInput, Option.bind_some] using h
  have eImageBefore := nativeSources_nonempty_endpoint_lt marked.valid marked.shapes atInput inputE sourceRun nonempty
  have eBefore : e < oldCursor := by
    by_contra failure
    have order := reach.names_strictMono.monotone (show oldCursor ≤ e by omega)
    omega
  have ve := Row.predecessor_lt_endpoint (entry.data.valid _ _ atOriginal) originalP originalE
  have eLower : a.length + k * (a.length - p) ≤ e := by omega
  have eUpper := eBefore.trans upper
  obtain ⟨endpointRow, atEndpoint⟩ := rowAt_exists (by omega : 0 < e)
    (eBefore.le.trans (rowAt_le_length atOriginal))
  obtain ⟨oldQ, atOldQ⟩ := fromRight_exists (xs := endpointRow.columns) (by decide : 0 < 2)
    (entry.data.valid _ _ atEndpoint).2.1
  have originalQ : penultimate initial e = some oldQ := by
    change endpointRow.q = some oldQ at atOldQ
    simp [penultimate, atEndpoint, atOldQ]
  have saturated := R.copies_cut_block_saturated hlast hp copies cut within
  have oldBound := saturated oldCursor row v e oldQ upper vInBlock atOriginal originalP originalE originalQ
  obtain ⟨q, atQ, alternatives⟩ := R.toMarkedRealization.copies_scan_q_last hlast hp copies cut within
    eLower eUpper atEndpoint atOldQ reach eBefore earlierRows (earlierSeeds e eLower eUpper eBefore)
  have qHistory : ∀ actual, penultimate current (names e) = some actual →
      actual = names oldQ ∨ actual + 1 = names (oldQ + 1) := by
    intro actual actualAt
    have same := Option.some.inj (actualAt.symm.trans atQ)
    subst actual
    exact alternatives
  obtain ⟨_, saved, record, exactSources⟩ := reach.native_record_inherits
    (earlierRows.priorSyntax entry.data.valid entry.data.shapes entry.proper)
    (by omega) (by omega) eBefore oldBound qHistory atInput inputP inputE sourceRun nonempty
  have pred : predecessor initial oldCursor = some v := by simp [predecessor, atOriginal, originalP]
  exact ⟨saved, record, exactSources, blockSeed_step pred (by omega) vInBlock⟩

end IBLP.BoundedRealization
