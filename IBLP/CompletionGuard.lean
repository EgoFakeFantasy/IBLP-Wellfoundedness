import IBLP.ScanRecords
import FullMarkedBLP.PacketAllEndpoints

namespace IBLP

theorem Trace.encode {a : Pattern} {target start : Nat} {rows : List Nat}
    (h : Trace a target start rows) : FullMarkedBLP.Trace (NativeBridge.encode a) target start rows := by
  induction h with
  | done => exact .stop
  | step lt pred _ inner ih => exact .next lt (by simpa only [NativeBridge.predecessor_encode] using pred) ih

namespace NativeBridge

theorem internalCheck_encode (a : Pattern) (trace : List Nat) :
    FullMarkedBLP.currentPlusOne (encode a) trace = IBLP.internalCheck a trace := by
  unfold FullMarkedBLP.currentPlusOne IBLP.internalCheck
  dsimp only
  congr 1
  funext pair
  rcases pair with ⟨parent, child⟩
  cases hr : IBLP.rowAt a parent <;> simp only [rowAt_encode, hr, Option.map_none, Option.map_some,
    Option.any_none, Option.any_some, encode_columns]

end NativeBridge

/-- The literal guard determines the endpoint at every internal arrow.
It says nothing yet about record existence or whole packet width. -/
theorem internalCheck_endpoints {a : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    {target start : Nat} {trace : List Nat} (h : Trace a target start trace)
    (guard : internalCheck a trace = true) :
    ∀ parent child, (parent, child) ∈ trace.dropLast.zip trace.dropLast.tail →
      ∃ row, rowAt a parent = some row ∧ row.p = some child ∧ row.e = some (child + 1) := by
  intro parent child pair
  obtain ⟨encodedRow, atEncoded, pred, endpoint⟩ := FullMarkedBLP.currentPlusOne_all_endpoints
    (NativeBridge.valid_encode valid shapes) h.encode
    ((NativeBridge.internalCheck_encode a trace).trans guard) parent child pair
  rw [NativeBridge.rowAt_encode] at atEncoded
  obtain ⟨row, hr, same⟩ := Option.map_eq_some_iff.mp atEncoded
  subst encodedRow
  exact ⟨row, hr, pred, endpoint⟩

theorem completionRecord_iff {a : Pattern} {rec : Records} {r mark : Nat} {sources : List Nat} :
    completionRecord a rec r mark = some sources ↔
      ∃ trace bottom, markTrace a r mark = some trace ∧ fromRight trace 2 = some bottom ∧
        recordAt rec bottom = some sources ∧ sources ≠ [] ∧ internalCheck a trace = true := by
  constructor
  · intro run
    obtain ⟨trace, computed, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨bottom, atBottom, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨ss, record, run⟩ := Option.bind_eq_some_iff.mp run
    split at run
    · simp at run
    · rename_i nonempty
      split at run
      · rename_i guard
        cases Option.some.inj run
        exact ⟨trace, bottom, computed, atBottom, record, by simpa only [List.isEmpty_iff] using nonempty, guard⟩
      · simp at run
  · rintro ⟨trace, bottom, computed, atBottom, record, nonempty, guard⟩
    simp only [completionRecord, computed, Bind.bind, Option.bind, atBottom, record,
      List.isEmpty_iff, nonempty, if_false, guard, if_true]

/-- A successful read always has a genuine retained birth event strictly
before the current cursor, even inside an arbitrary frozen prefix. -/
theorem ScanReach.completion_record_origin {initial current : Pattern} {start cursor mark : Nat}
    {rec : Records} (reach : ScanReach initial start current rec cursor) (processed : List Nat)
    {sources : List Nat}
    (run : completionRecord (processed.foldl (fun a b => completeMark a rec cursor b) current) rec cursor mark = some sources) :
    ∃ bottom, (bottom, sources) ∈ rec ∧ sources ≠ [] ∧ bottom + sources.length < cursor := by
  obtain ⟨_, bottom, _, _, record, nonempty, _⟩ := completionRecord_iff.mp run
  exact ⟨bottom, recordAt_mem record, nonempty, reach.lookup_before record⟩

end IBLP
