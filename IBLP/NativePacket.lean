import IBLP.NativeWalk
import IBLP.ScanRecords

namespace IBLP

/-- The exact descending source record in manuscript 6.3. -/
def descendingPacket (base width : Nat) : List Nat :=
  (List.range width).reverse.map (fun j => base + j + 1)

theorem descendingPacket_length (base width : Nat) : (descendingPacket base width).length = width := by
  simp [descendingPacket]

theorem descendingPacket_reverse (base width : Nat) :
    (descendingPacket base width).reverse = (List.range width).map (fun j => base + j + 1) := by
  simp [descendingPacket, ← List.map_reverse]

theorem NativeWalk.unique {a : Pattern} {p entrance : Nat} {xs ys : List Nat}
    (left : NativeWalk a p entrance xs) (right : NativeWalk a p entrance ys) : xs = ys := by
  induction left generalizing ys with
  | stop edge below =>
    cases right with
    | stop => rfl
    | step other above rest =>
      have same := Option.some.inj (edge.symm.trans other)
      omega
  | step edge above rest ih =>
    cases right with
    | stop other below =>
      have same := Option.some.inj (edge.symm.trans other)
      omega
    | step other _ next =>
      have same := Option.some.inj (edge.symm.trans other)
      subst same
      exact congrArg (_ :: ·) (ih next)

theorem NativeWalk.packet {a : Pattern} {base width entrance : Nat}
    (entry : penultimate a entrance = some (base + width))
    (family : ∀ j, 0 < j → j ≤ width → penultimate a (base + j) = some (base + j - 1)) :
    NativeWalk a base entrance (descendingPacket base width) := by
  induction width generalizing entrance with
  | zero => exact .stop entry (by omega)
  | succ width ih =>
    have next : penultimate a (base + (width + 1)) = some (base + width) := by
      simpa only [Nat.add_sub_cancel] using family (width + 1) (by omega) (by omega)
    have tail := ih next (fun j positive bound => family j positive (by omega))
    have full := NativeWalk.step entry (by omega : base < base + (width + 1)) tail
    simpa only [descendingPacket, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.map_append, List.map_cons, List.map_nil, List.singleton_append, Nat.add_assoc] using full

theorem nativeSources_eq_packet {a : Pattern} {owner base endpoint width : Nat} {row : Row}
    {sources : List Nat} (atRow : rowAt a owner = some row) (hp : row.p = some base)
    (he : row.e = some endpoint) (eligible : row.columns.length ≤ 2 * row.step)
    (run : nativeSources a owner = some sources)
    (entry : penultimate a endpoint = some (base + width))
    (family : ∀ j, 0 < j → j ≤ width → penultimate a (base + j) = some (base + j - 1)) :
    sources = descendingPacket base width := by
  rcases nativeSources_spec atRow run with ⟨long, _⟩ | ⟨_, p, e, atP, atE, walk⟩
  · omega
  · have sameP := Option.some.inj (atP.symm.trans hp)
    have sameE := Option.some.inj (atE.symm.trans he)
    subst p
    subst e
    exact walk.unique (NativeWalk.packet entry family)

/-- An actual saved family supplies every q link, including the final
stop at its owner. Only the endpoint's exact first q remains to identify
in the record-inheritance argument. -/
theorem ScanReach.frozen_nativeSources_packet {initial current : Pattern} {start cursor base endpoint : Nat}
    {rec : Records} {saved result : List Nat} {row : Row}
    (reach : ScanReach initial start current rec cursor) (history : ScanPriorSyntax initial start cursor)
    (record : (base, saved) ∈ rec)
    (atRow : rowAt (completeFrozenMarks current rec cursor) cursor = some row)
    (hp : row.p = some base) (he : row.e = some endpoint) (eligible : row.columns.length ≤ 2 * row.step)
    (run : nativeSources (completeFrozenMarks current rec cursor) cursor = some result)
    (entry : penultimate (completeFrozenMarks current rec cursor) endpoint = some (base + saved.length)) :
    result = descendingPacket base saved.length := by
  apply nativeSources_eq_packet atRow hp he eligible run entry
  intro j positive bound
  have behind := reach.record_family_before record
  simpa only [penultimate, completeFrozenMarks_other_row (by omega : base + j ≠ cursor)] using
    reach.record_target_q history record positive bound

end IBLP
