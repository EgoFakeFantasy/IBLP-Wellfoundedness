import IBLP.NativeNonempty
import IBLP.NativePacket
import IBLP.ScanEmptyRecord

namespace IBLP

/-- The first-q part of manuscript 6.3. Entrance conditional saturation
gives oldQ <= v. The prior q-family alternatives exclude oldQ < v;
then the actual family at v determines the whole new source record. -/
theorem ScanLabeledReach.native_record_inherits {initial current : Pattern}
    {scanStart oldCursor v e oldQ : Nat} {rec : Records} {names : Nat → Nat}
    {row : Row} {sources : List Nat}
    (reach : ScanLabeledReach initial scanStart current rec oldCursor names)
    (priorSyntax : ScanPriorSyntax initial scanStart (names oldCursor))
    (vScanned : scanStart ≤ v) (vProcessed : v < oldCursor) (eProcessed : e < oldCursor)
    (oldBound : oldQ ≤ v)
    (qHistory : ∀ q, penultimate current (names e) = some q →
      q = names oldQ ∨ q + 1 = names (oldQ + 1))
    (atRow : rowAt (completeFrozenMarks current rec (names oldCursor)) (names oldCursor) = some row)
    (hp : row.p = some (names v)) (he : row.e = some (names e))
    (run : nativeSources (completeFrozenMarks current rec (names oldCursor)) (names oldCursor) = some sources)
    (nonempty : sources ≠ []) :
    oldQ = v ∧ ∃ saved, (names v, saved) ∈ rec ∧
      sources = descendingPacket (names v) saved.length := by
  obtain ⟨eligible, q, atQ, above⟩ := nativeSources_nonempty_first atRow hp he run nonempty
  have before := reach.names_strictMono eProcessed
  have currentQ : penultimate current (names e) = some q := by
    simpa only [penultimate, completeFrozenMarks_other_row (by omega : names e ≠ names oldCursor)] using atQ
  have alternatives := qHistory q currentQ
  have eqOld : oldQ = v := by
    by_contra different
    have nextLe := reach.names_strictMono.monotone (show oldQ + 1 ≤ v by omega)
    have oldLe := reach.names_strictMono.monotone oldBound
    rcases alternatives with same | next <;> omega
  subst oldQ
  have atNext : q + 1 = names (v + 1) := alternatives.resolve_left (by omega)
  obtain ⟨saved, record, neighbors⟩ : ∃ saved, (names v, saved) ∈ rec ∧
      names (v + 1) = names v + saved.length + 1 := by
    rcases reach.record_or_adjacent vScanned vProcessed with adjacent | recorded
    · omega
    · exact recorded
  have first : penultimate (completeFrozenMarks current rec (names oldCursor)) (names e) =
      some (names v + saved.length) := by
    convert atQ using 1
    congr 1
    omega
  exact ⟨rfl, saved, record,
    reach.forget.frozen_nativeSources_packet priorSyntax record atRow hp he eligible run first⟩

end IBLP
