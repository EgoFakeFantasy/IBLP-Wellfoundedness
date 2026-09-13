import IBLP.NativeBlockStrongMarks

namespace IBLP

theorem Row.shiftAfter_properMark {row : Row} {mark : Nat} (proper : row.ProperMark mark)
    (r h : Nat) : (row.shiftAfter r h).ProperMark (IBLP.shiftAfter r h mark) := by
  obtain ⟨k, entry, positive, before⟩ := proper
  refine ⟨k, ?_, positive, ?_⟩
  · change (row.columns.map (IBLP.shiftAfter r h))[k]? = _
    simp only [List.getElem?_map, entry, Option.map_some]
  · simpa only [Row.shiftAfter, List.length_map] using before

theorem native_preserves_proper {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    (proper : ProperMarks a) {r : Nat} {sources : List Nat} (run : native a r = some (b, sources)) :
    ProperMarks b := by
  obtain ⟨row, hr, rest⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨ss, sourceRun, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨block, blockRun, out⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj out
  intro result member
  rcases List.mem_append.mp member with earlier | later
  · rcases List.mem_append.mp earlier with old | family
    · exact proper result (List.mem_of_mem_take old)
    · exact nativeBlock_proper valid shapes hr sourceRun (proper row (rowAt_mem hr)) blockRun result family
  · obtain ⟨old, oldMember, same⟩ := List.mem_map.mp later
    subst result
    intro mark marked
    obtain ⟨oldMark, oldMarked, same⟩ := List.mem_map.mp marked
    subst mark
    exact Row.shiftAfter_properMark (proper old (List.mem_of_mem_drop oldMember) oldMark oldMarked) r sources.length

/-- The exact native output retains the original basic array invariant.
The positive source-position condition is proved locally, and supplies
mark membership without strengthening the input to sorted mark lists. -/
theorem native_preserves_basic {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    (proper : ProperMarks a) {r : Nat} {sources : List Nat} (run : native a r = some (b, sources)) :
    BasicValid b := by
  have encodedRun : FullMarkedBLP.native (NativeBridge.encode a) r = some (NativeBridge.encode b, sources) := by
    rw [NativeBridge.native_encode, run]
    rfl
  have encodedValid := FullMarkedBLP.native_preserves_coreValid (NativeBridge.valid_encode valid shapes) encodedRun
  have newProper := native_preserves_proper valid shapes proper run
  intro owner row hr
  have encodedRow : FullMarkedBLP.rowAt (NativeBridge.encode b) owner = some (NativeBridge.encodeRow row) := by
    simp only [NativeBridge.rowAt_encode, hr, Option.map_some]
  exact NativeBridge.decoded_basic_of_proper (encodedValid _ _ encodedRow) (newProper row (rowAt_mem hr))

theorem native_preserves_syntax {a b : Pattern} (valid : BasicValid a) (shapes : OrdinaryShape a)
    (proper : ProperMarks a) {r : Nat} {sources : List Nat} (run : native a r = some (b, sources)) :
    BasicValid b ∧ OrdinaryShape b ∧ ProperMarks b :=
  ⟨native_preserves_basic valid shapes proper run,
    native_preserves_shapes valid shapes run, native_preserves_proper valid shapes proper run⟩

end IBLP
