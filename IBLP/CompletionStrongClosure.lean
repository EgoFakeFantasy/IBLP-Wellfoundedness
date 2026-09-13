import IBLP.CompletionGeometry
import IBLP.MappedIndices

namespace IBLP.Row.CompletionGeometry

variable {row : Row} {owner mark : Nat} {sources : List Nat}
variable (C : row.CompletionGeometry owner mark sources)
include C

theorem sources_below_proper (valid : row.BasicValid owner) (shape : row.OrdinaryShape)
    {z : Nat} (proper : row.ProperMark z) : ∀ x ∈ sources, x < z := by
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.columns) (k := row.step + 1)
    (by omega) (by have := Row.step_lt_length shape; omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.columns) (Row.step_pos shape)
    (Row.step_lt_length shape).le
  have old : (NativeBridge.encodeRow row).CoreValid owner :=
    ⟨valid.1, valid.2.1, valid.2.2.1, NativeBridge.shape_encode shape⟩
  have pe := FullMarkedBLP.row_p_lt_e old hp he
  have ez := Row.properMark_above_e valid.1 shape proper he
  exact fun x hx => (C.sources_below_p valid.1 shape hp x hx).trans (pe.trans ez)

theorem old_proper (valid : row.BasicValid owner) (shape : row.OrdinaryShape)
    {z : Nat} (proper : row.ProperMark z) :
    (completeMarkRow row mark sources).ProperMark z := by
  have bound := Row.properMark_lt valid proper
  have below := C.sources_below_proper valid shape proper
  obtain ⟨k, atZ, positive, _⟩ := proper
  have rank := FullMarkedBLP.sorted_rank_at_index valid.1 atZ
  have growth := FullMarkedBLP.completeMarkRow_rank_bound (row := NativeBridge.encodeRow row)
    (y := mark) (valid.1.imp Nat.ne_of_lt) C.distinct (C.disjoint valid.1) below
  have member : z ∈ (FullMarkedBLP.completeMarkRow (NativeBridge.encodeRow row) mark sources).core :=
    (FullMarkedBLP.completeMarkRow_core_mem _ _ _ _).mpr (Or.inl (List.mem_of_getElem? atZ))
  have entry := FullMarkedBLP.sorted_get_at_rank
    (FullMarkedBLP.completeMarkRow_sorted (NativeBridge.encodeRow row) mark sources).1 member
  simp only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_columns] at growth entry
  change _ + sources.length ≤ _ at growth
  rw [rank] at growth
  exact Row.properMark_of_index (C.encoded_valid valid shape).2.2.1 bound entry
    (by change row.step + sources.length + 1 ≤ _; omega)

theorem new_proper (valid : row.BasicValid owner) (shape : row.OrdinaryShape)
    {j : Nat} (hj : j < sources.length) :
    (completeMarkRow row mark sources).ProperMark (mark + (j + 1)) := by
  have entry := FullMarkedBLP.completeMarkRow_targets_entry (row := NativeBridge.encodeRow row)
    valid.1 C.distinct (C.disjoint valid.1) C.target_gap C.mark_at
    (C.sources_below_mark valid.1 shape) (j := j + 1) (by omega)
  simp only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_columns] at entry
  exact Row.properMark_of_index (C.encoded_valid valid shape).2.2.1
    (by have := C.before_owner; omega) entry
    (by change row.step + sources.length + 1 ≤ _; have := C.positive; omega)

/-- All marks satisfy the original stronger condition, with no ordering or
uniqueness premise on the old mark list. -/
theorem all_proper (valid : row.BasicValid owner) (shape : row.OrdinaryShape)
    (proper : ∀ z ∈ row.marks, row.ProperMark z) :
    ∀ z ∈ (completeMarkRow row mark sources).marks,
      (completeMarkRow row mark sources).ProperMark z := by
  intro z hz
  simp only [completeMarkRow, mem_canonicalColumns, List.mem_append] at hz
  rcases hz with old | new
  · exact C.old_proper valid shape (proper z (List.mem_filter.mp old).1)
  · obtain ⟨j, hj, same⟩ := List.mem_map.mp new
    have hj := List.mem_range.mp hj
    have he : mark + (j + 1) = z := by omega
    exact he ▸ C.new_proper valid shape hj

theorem basic_valid (valid : row.BasicValid owner) (shape : row.OrdinaryShape)
    (proper : ∀ z ∈ row.marks, row.ProperMark z) :
    (completeMarkRow row mark sources).BasicValid owner :=
  NativeBridge.decoded_basic_of_proper (C.encoded_valid valid shape) (C.all_proper valid shape proper)

/-- The exact q update needed for the later record-inheritance argument.
Only completion at the old penultimate value changes that value. -/
theorem q_update (valid : row.BasicValid owner) (shape : row.OrdinaryShape)
    {q : Nat} (hq : row.q = some q) :
    (completeMarkRow row mark sources).q = some (q + if mark = q then sources.length else 0) := by
  have atQ : row.columns[row.columns.length - 2]? = some q := by
    simpa only [Row.q, fromRight, show 0 < 2 ∧ 2 ≤ row.columns.length from ⟨by decide, valid.2.1⟩,
      if_true] using hq
  have markLe := Row.column_index_le valid.1 C.mark_at atQ (by have := C.notLast; omega)
  have length := C.length valid.1 shape
  have oldLength := valid.2.1
  by_cases same : mark = q
  · subst q
    have index : C.index = row.columns.length - 2 := by
      have left := sorted_idxOf_of_at valid.1 C.mark_at
      have right := sorted_idxOf_of_at valid.1 atQ
      omega
    have entry := FullMarkedBLP.completeMarkRow_targets_entry (row := NativeBridge.encodeRow row)
      valid.1 C.distinct (C.disjoint valid.1) C.target_gap C.mark_at
      (C.sources_below_mark valid.1 shape) (j := sources.length) (by omega)
    simp only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_columns] at entry
    have equalIndex : C.index + sources.length + sources.length =
        row.columns.length + 2 * sources.length - 2 := by omega
    rw [equalIndex] at entry
    simpa only [Row.q, fromRight, length,
      show 0 < 2 ∧ 2 ≤ row.columns.length + 2 * sources.length by omega, if_true] using entry
  · have high : mark + sources.length < q := by
      by_contra hn
      exact C.target_gap q (by omega) (by omega) (List.mem_of_getElem? atQ)
    have entry := FullMarkedBLP.completeMarkRow_high_entry (row := NativeBridge.encodeRow row)
      valid.1 C.distinct (C.disjoint valid.1)
      (fun x hx => (C.sources_below_mark valid.1 shape x hx).le) C.target_gap atQ high
    simp only [NativeBridge.completeMarkRow_encode, NativeBridge.encode_columns] at entry
    have equalIndex : row.columns.length - 2 + 2 * sources.length =
        row.columns.length + 2 * sources.length - 2 := by omega
    rw [equalIndex] at entry
    simpa only [Row.q, fromRight, length,
      show 0 < 2 ∧ 2 ≤ row.columns.length + 2 * sources.length by omega,
      if_true, same, if_false, Nat.add_zero] using entry

end IBLP.Row.CompletionGeometry
