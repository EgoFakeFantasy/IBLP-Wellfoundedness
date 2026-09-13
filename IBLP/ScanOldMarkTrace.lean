import IBLP.FrozenMarkTrace
import IBLP.ScanGeometryHistory
import IBLP.NativeRows
import IBLP.CompletionGuard

namespace IBLP

/-- Exact transport of an already computed trace in a later carrier row.
The complete trace, including its paired source, uses the same native shift. -/
theorem native_suffix_computed_markTrace {a b : Pattern} (valid : BasicValid a)
    (shapes : OrdinaryShape a) {owner carrier mark : Nat} {sources rows : List Nat}
    (run : native a owner = some (b, sources)) (after : owner < carrier)
    (computed : markTrace a carrier mark = some rows) :
    markTrace b (carrier + sources.length) (shiftAfter owner sources.length mark) =
      some (rows.map (shiftAfter owner sources.length)) := by
  obtain ⟨row, k, source, atRow, legal, atMark, atSource, trace⟩ := markTrace_pair_data computed
  have atNew : rowAt b (carrier + sources.length) = some (row.shiftAfter owner sources.length) := by
    rw [native_suffix_rowAt run after, atRow]
    rfl
  have sorted : (row.shiftAfter owner sources.length).columns.Pairwise (· < ·) := by
    change (row.columns.map (shiftAfter owner sources.length)).Pairwise (· < ·)
    rw [List.pairwise_map]
    exact (valid _ _ atRow).1.imp (fun h => shiftAfter_strictMono owner sources.length h)
  apply markTrace_of_pair atNew sorted legal (k := k) (source := shiftAfter owner sources.length source)
  · change (row.columns.map (shiftAfter owner sources.length))[k]? = _
    simp only [List.getElem?_map, atMark, Option.map_some]
  · change (row.columns.map (shiftAfter owner sources.length))[k - row.step]? = _
    simp only [List.getElem?_map, atSource, Option.map_some]
  · exact trace.native_shift valid shapes run

/-- An original mark on a carrier not yet natively expanded keeps its
whole computed trace under every strictly earlier event. In particular an
entrance crossing bottom cannot turn into a newly active old bottom. -/
theorem ScanLabeledReach.unprocessed_markTrace {initial current : Pattern}
    {start oldCursor carrier mark : Nat} {rec : Records} {names : Nat → Nat} {rows : List Nat}
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : ScanPriorGeometry initial start (names oldCursor))
    (unprocessed : oldCursor ≤ carrier) (computed : markTrace initial carrier mark = some rows) :
    markTrace current (names carrier) (names mark) = some (rows.map names) := by
  induction reach with
  | start => simpa only [id_eq, List.map_id] using computed
  | @next before after records old name sources previous bound run ih =>
    have earlier : name old < (shiftAfter (name old) sources.length ∘ name) (old + 1) := by
      rw [previous.next_cursor]
      omega
    have earlierHistory := history.mono earlier.le
    have oldTrace := ih earlierHistory (by omega)
    have oldSyntax := previous.forget.syntax_of_geometry valid shapes proper earlierHistory
    have marksHistory := history before records (name old) previous.forget earlier
    have marked := completeFrozenMarks_invariant oldSyntax.1 oldSyntax.2.1 oldSyntax.2.2 marksHistory
    have retained := completeFrozenMarks_markTrace oldSyntax.1 oldSyntax.2.1 oldSyntax.2.2 marksHistory oldTrace
    have behind := previous.names_strictMono (by omega : old < carrier)
    have result := native_suffix_computed_markTrace marked.valid marked.shapes run behind retained
    simpa only [Function.comp_apply, shiftAfter, if_pos behind, List.map_map] using result

theorem fromRight_map (f : Nat → Nat) (xs : List Nat) (k : Nat) :
    fromRight (xs.map f) k = (fromRight xs k).map f := by
  simp only [fromRight, List.length_map, List.getElem?_map]
  split <;> simp_all

/-- At an actual frozen prefix of the current old row, every entrance
trace still has its exact old-label image, including its bottom factor. -/
theorem ScanLabeledReach.frozen_markTrace {initial before current : Pattern}
    {start oldCursor mark : Nat} {rec : Records} {names : Nat → Nat}
    {pending rows : List Nat}
    (reach : ScanLabeledReach initial start before rec oldCursor names)
    (frozen : FrozenReach before rec (names oldCursor) current pending)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (earlierRows : ScanPriorGeometry initial start (names oldCursor))
    (earlierMarks : FrozenGeometryBefore before rec (names oldCursor) pending.length)
    (computed : markTrace initial oldCursor mark = some rows) :
    markTrace current (names oldCursor) (names mark) = some (rows.map names) := by
  have oldSyntax := reach.forget.syntax_of_geometry valid shapes proper earlierRows
  exact frozen.markTrace oldSyntax.1 oldSyntax.2.1 oldSyntax.2.2 earlierMarks
    (reach.unprocessed_markTrace valid shapes proper earlierRows (Nat.le_refl _) computed)

/-- An old crossing bottom is still in the untouched entrance prefix.
Consequently the literal completion guard cannot obtain a saved record
for it, even after earlier marks on this same row have been completed. -/
theorem ScanLabeledReach.crossing_completionRecord_none {initial before current : Pattern}
    {start oldCursor mark bottom : Nat} {rec : Records} {names : Nat → Nat}
    {pending rows : List Nat}
    (reach : ScanLabeledReach initial start before rec oldCursor names)
    (frozen : FrozenReach before rec (names oldCursor) current pending)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (earlierRows : ScanPriorGeometry initial start (names oldCursor))
    (earlierMarks : FrozenGeometryBefore before rec (names oldCursor) pending.length)
    (computed : markTrace initial oldCursor mark = some rows)
    (bottomAt : fromRight rows 2 = some bottom) (crossing : bottom < start) :
    completionRecord current rec (names oldCursor) (names mark) = none := by
  have retained := reach.frozen_markTrace frozen valid shapes proper earlierRows earlierMarks computed
  have bottomImage : fromRight (rows.map names) 2 = some (names bottom) := by
    rw [fromRight_map, bottomAt]
    rfl
  cases run : completionRecord current rec (names oldCursor) (names mark) with
  | none => rfl
  | some sources =>
    obtain ⟨trace, actualBottom, traceAt, actualAt, record, _, _⟩ := completionRecord_iff.mp run
    have sameTrace : trace = rows.map names := Option.some.inj (traceAt.symm.trans retained)
    rw [sameTrace, bottomImage] at actualAt
    have sameBottom := Option.some.inj actualAt
    rw [← sameBottom] at record
    exact False.elim (reach.no_record_before_start crossing sources (recordAt_mem record))

end IBLP
